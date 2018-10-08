#include "blimit.hpp"
#include <iostream>
#include <fstream>
#include <sstream>
#include <regex>
#include <utility>
#include <unordered_map>
#include <unordered_set>
#include <set>
#include <vector>
#include <cassert>
#include <chrono>
#include <atomic>
#include <thread>

#define st first
#define nd second
#define sz(w) (int) w.size()

class edge_t {
public:
  int weight;
  int node;
  
  edge_t() = default;
  edge_t(int _weight, int _node) : weight(_weight), node(_node) {}
  
  bool operator()(const edge_t& e, const edge_t& f) {
    return e.weight > f.weight || (e.weight == f.weight && e.node > f.node);
  }
};

using namespace std;
using edge_set_t = set<edge_t, edge_t>;/// <weight, neighbour id, if is adoring>

const regex correct_line("^[0-9 ]*$");
const int NOT_FOUND = -1;
unordered_map<int, edge_set_t> graph;/// lists of <weight, neighbour node id,
                                     /// if neighbour is adoring>
unordered_map<int, edge_set_t> adorators;/// S
vector<int> cur_nodes;/// Q
unordered_set<int> rest_of_nodes;/// R
unordered_map<int, int> b;/// adorators left to find
unordered_map<int, int> bval;/// == bvalue
unordered_map<int, atomic<int>> global_db;/// delta b
chrono::duration<long int> global_duration;

atomic_flag lock = ATOMIC_FLAG_INIT;
unordered_map<int, atomic_flag> locks;

void init_structures(unsigned int b_method) {
  for (auto& map_el : graph) {
    cur_nodes.push_back(map_el.st);
    bval[map_el.st] = bvalue(b_method, map_el.st);
    global_db[map_el.st].store(0);
  }
  b = bval;
}

void cleanup() {
  for (auto& map_el : graph) {
    b[map_el.st] = global_db[map_el.st].load();
    global_db[map_el.st] = 0;
  }
  cur_nodes.clear();
  for (int node : rest_of_nodes) {
    cur_nodes.push_back(node);
  }
  rest_of_nodes.clear();
}

inline bool check_adorators_full(int node) {
  return sz(adorators[node]) == bval[node];
}

int sum_of_weights() {
  //iter po adorators
  int sum = 0;
  for (auto& map_el : adorators) {
    for (const edge_t& edge : map_el.nd) {
      sum += edge.weight;
    }
  }
  
  return sum / 2;
}

/// if no last: {0, NOT_FOUND}
edge_t last_adorator(int node) {
  if (bval[node] != 0 && check_adorators_full(node)) {
    return *(--adorators[node].end());
  }
  return {0, NOT_FOUND};
}

bool check_eligibility(edge_t edge, int cur_node) {
  auto& adors = adorators[edge.node];
  return
    (bval[edge.node] != 0 &&
     adors.find({edge.weight, cur_node}) == adors.end() &&
     (!check_adorators_full(edge.node) || adors.empty() ||
      edge.weight > (--adors.end())->weight ||
      (edge.weight == (--adors.end())->weight && cur_node > (--adors.end())->node)));
}

/// if not found: {0, NOT_FOUND}
edge_t find_argmax(int cur_node) {
  for (auto cand_it = graph[cur_node].begin(); cand_it != graph[cur_node].end(); ++cand_it) {
    if (check_eligibility(*cand_it, cur_node)) {
      return *cand_it;
    }
  }
  return {0, NOT_FOUND};
}

void calculate_tasks(int first, int last) { // [first, last]
  for (int i = first; i < last; ++i) {
    int cur_node = cur_nodes[i];
    int count = 0;
    
    while (count < b[cur_node]) {
      edge_t argmax_edge = find_argmax(cur_node);
      
      if (argmax_edge.node == NOT_FOUND) {//cout<<"no argmax\n";
        break;
      }
      
      while (locks[argmax_edge.node].test_and_set()) {
      }
      
      if (!check_eligibility(argmax_edge, cur_node)) {
        locks[argmax_edge.node].clear();
      }
      else {
        ++count;
        int argmax = argmax_edge.node;//cout<<"argmax = "<<argmax<<endl;// x
        edge_t last_edge = last_adorator(argmax);
        adorators[argmax].emplace(argmax_edge.weight, cur_node);// S[x].insert(u)
        
        if (last_edge.node != NOT_FOUND) {
          adorators[argmax].erase(last_edge);// S[x] `implicite` delete
          
          if (global_db[last_edge.node].load() == 0) {
            while (lock.test_and_set()) {
            }
            
            if (global_db[last_edge.node].load() == 0) {
              rest_of_nodes.insert(last_edge.node);
            }
            lock.clear();
          }
          global_db[last_edge.node]++;
        }
        locks[argmax].clear();
      }
    }
  }
}

vector<pair<int, int>> make_tasks(unsigned int thread_count) {
  vector<pair<int, int>> tasks;
  int part = sz(cur_nodes) / thread_count;
  int ready = 0;
  
  for (unsigned int i = 0; i < thread_count - 1; ++i, ready += part) {
    tasks.emplace_back(ready, ready + part);
  }
  tasks.emplace_back(ready, sz(cur_nodes));
  
  return tasks;
}

int b_suitor(unsigned int b_method, int thread_count) {
  init_structures(b_method);
  
  chrono::high_resolution_clock::time_point t1 =
    chrono::high_resolution_clock::now();
  
  while (!cur_nodes.empty()) {
    vector<thread> threads;
    vector<pair<int, int>> tasks = make_tasks(thread_count);
    
    for (int i = 0; i < sz(tasks) - 1; ++i) {
      threads.emplace_back(calculate_tasks, tasks[i].first, tasks[i].second);
      threads[i].join();
    }
    calculate_tasks(tasks[sz(tasks) - 1].first, tasks[sz(tasks) - 1].second);
    
    cleanup();
  }
  
  int sum = sum_of_weights();
  
  chrono::high_resolution_clock::time_point t2 =
    chrono::high_resolution_clock::now();
  auto len = chrono::duration_cast<chrono::seconds>( t2 - t1 );
  global_duration += len;
  cerr << "b_method " << b_method << " time = " << len.count() << endl;
  
  adorators.clear(); cur_nodes.clear(); bval.clear();
  
  return sum;
}

void make_graph(string& input_filename) {
  ifstream file(input_filename);
  if (!file)
    exit(2);
  
  string line;
  while (getline(file, line)) {
    if (regex_match(line, correct_line)) {
      int node1, node2, weight;
      stringstream stream(line);
      stream >> node1 >> node2 >> weight;
      
      graph[node1].emplace(weight, node2);
      graph[node2].emplace(weight, node1);
    }
  }
  
  file.close();
  
  for (auto& map_el : graph) {
    locks[map_el.st].clear();
  }
}

int main(int argc, char* argv[]) {
  if (argc != 4) {
    cerr << "usage: " << argv[0] << " thread-count inputfile b-limit" << endl;
    return 1;
  }

  int thread_count = stoi(argv[1]);
  int b_limit = stoi(argv[3]);
  string input_filename{argv[2]};
  
  make_graph(input_filename);
  
  for (int b_method = 0; b_method < b_limit + 1; ++b_method)
    cout << b_suitor(b_method, thread_count) << endl;
    
  cerr << "Global duration = " << global_duration.count() << endl;
}

