#include <iostream>
#include <vector>
#include <unordered_map>
#include <fstream>
#include <sstream>
#include <functional>
#include <queue>
#include <list>
#include <algorithm>
#include <set>
#include <map>
#include <thread>
#include <mutex>
#include <atomic>
#include "blimit.hpp"
#include <condition_variable>


using pair_uu = std::pair<unsigned, unsigned>;
using vector_puu = std::vector<pair_uu>;
using std_graph = std::vector<std::pair<unsigned, std::vector<pair_uu >>>;
using ud_graph = std::map<unsigned, vector_puu, std::greater<>>;
using u_queue = std::queue<unsigned, std::list<unsigned>>;
using set_puu_desc = std::set<pair_uu, std::greater<>>;
using set_puu_inc = std::set<pair_uu>;
using map_of_sets_desc = std::unordered_map<unsigned, set_puu_desc>;
using map_of_sets_inc = std::unordered_map<unsigned, std::set<pair_uu>>;


void read_input(std_graph &graph_vec, std::vector<unsigned>& old_values, const std::string &file_name) {
    std::ifstream data;
    std::string s;
    unsigned node1, node2, vague;
    ud_graph graph_map;
    data.open(file_name);
    if (data.is_open()) {
        while (getline(data, s)) {
            if (s.front() == '#')
                continue;

            std::stringstream SS(s);
            SS >> node1; SS >> node2; SS >> vague;

            graph_map.insert(std::make_pair(node1, std::vector<std::pair<unsigned, unsigned>>()));
            graph_map.insert(std::make_pair(node2, std::vector<std::pair<unsigned, unsigned>>()));
            graph_map[node1].emplace_back(std::make_pair(node2, vague));
            graph_map[node2].emplace_back(std::make_pair(node1, vague));
        }
    }

    for (auto& vertex : graph_map) {
        graph_vec.emplace_back(vertex);
        old_values.push_back(0);
    }

    std::unordered_map<unsigned, unsigned> vertexes_reverse;
    unsigned i = 0;
    for (auto& vertex : graph_vec) {
        vertexes_reverse.insert(std::make_pair(vertex.first, i));
        old_values[i] = vertex.first;
        vertex.first = i;
        ++i;
    }
    for (auto& vertex : graph_vec) {
        for (auto& edge : vertex.second) {
            edge.first = vertexes_reverse[edge.first];
        }
    }
}

void check_correctness() {

    std::ifstream wzorce, wyniki;
    std::string swynik, swzorzec;
    wzorce.open("../data/wzorce.txt");
    wyniki.open("../data/wyniki_seq.txt");
    int dobre = 0, zle = 0;
    while (getline(wzorce, swzorzec) && getline(wyniki, swynik)) {
        if (swynik != swzorzec) {
            zle++;
        } else {
            dobre++;
        }
    }
    std::cout << dobre << " dobrze, " << zle << " zle" << std::endl;

}

static void create_info(const std_graph& graph, std::vector<set_puu_desc>& T,
                        std::vector<set_puu_desc>& N, std::vector<set_puu_desc>&S,
                        std::vector<set_puu_desc>& N_T, u_queue& Q) {

    for (const auto &vertex : graph) {
        S.emplace_back(set_puu_desc());
        T.emplace_back(set_puu_desc());
        N_T.emplace_back(set_puu_desc());
        N.emplace_back(set_puu_desc());
        for (const auto &edge : vertex.second) {
            N_T[vertex.first].insert(std::make_pair(edge.second, edge.first));
            N[vertex.first].insert((std::make_pair(edge.second, edge.first)));
        }
    }

    for (auto i = (long) graph.size()-1; i >= 0; --i) {
        Q.push(graph[i].first);
    }
}

pair_uu search_to_suite(const std::vector<set_puu_desc>& N_T,
                        const std::vector<set_puu_desc>& S, unsigned b_u, unsigned u, std::vector<unsigned>& old_values) {
    for (const auto &ntq : N_T[u]) {
        const auto& s_last = S.at(ntq.second).rbegin();
        auto &s_x = S.at(ntq.second);
        if (bvalue(b_u, old_values[ntq.second]) == 0)
            continue;
        if (s_x.size() < bvalue(b_u, old_values[ntq.second]) || !((ntq.first < s_last->first) ||
                                                      (ntq.first == s_last->first &&
                                                       u < s_last->second))) {
            return std::make_pair(ntq.first, ntq.second);
        } else {
            continue;
        }
    }
    return {0, 0};
}

static void remove_worse_adorer(set_puu_desc& s_x, std::vector<set_puu_desc>& T, u_queue& R, pair_uu& x) {
    pair_uu y;
    auto it = s_x.rbegin();
    y = std::make_pair(it->first, it->second);
    s_x.erase(*it);
    T[y.second].erase({y.first, x.second});
    R.push(y.second);
}

static void insert_adorer(set_puu_desc& s_x, std::vector<set_puu_desc>& N_T, std::vector<set_puu_desc>& T, pair_uu x,
                          unsigned u) {
    s_x.insert(std::make_pair(x.first, u));
    N_T[u].erase(x);
    T[u].insert(x);
}

unsigned count_edges(std::vector<set_puu_desc>& S) {
    unsigned result{0};
    for (int i = 0; i < S.size(); ++i) {
        for (auto &pair : S[i]) {
            auto &s_x = S.at(pair.second);
            if (s_x.count({pair.first, i})) {
                result += pair.first;
                s_x.erase({pair.first, i});
            }
        }
    }
    return result;
}

unsigned adorate_sequential(const std_graph &graph, unsigned b_u, std::vector<unsigned>& old_values) {
    u_queue Q, R;
    std::vector<set_puu_desc> S, N_T, T, N;
    pair_uu x;

    create_info(graph, T, N, S, N_T, Q);

    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    while (!Q.empty()) {
        unsigned long qsize = Q.size();
        for (unsigned long i = qsize; i > 0; --i) {
            unsigned u = Q.front();
            Q.pop();
            while (T[u].size() < bvalue(b_u, old_values[u])) {
                if (N_T.at(u).empty()) {
                    break;
                }
                x = search_to_suite(N_T, S, b_u, u, old_values);

                if (x.first == 0) {
                    break;
                }
                auto & s_x = S.at(x.second);
                if (s_x.size() == bvalue(b_u, old_values[x.second])) {
                    remove_worse_adorer(s_x, T, R, x);
                }
                insert_adorer(s_x, N_T, T, x, u);
            }
        }
        Q = R;
        R = u_queue();
    }

    unsigned result = count_edges(S);
    std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
    std::cout << "Time : " << std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count() <<std::endl;
    return result;
}



int main(int argc, const char * argv[]) {
    if (argc != 4)
        std::exit(1);
    std::string file_name = argv[2];
    unsigned b_limit =  (unsigned) std::stoul(argv[3]);
    std_graph graph;
    std::vector<unsigned> old_values;
    read_input(graph, old_values, file_name);

    std::set<std::pair<unsigned, unsigned>> sett;

    std::ofstream outfile ("../data/wyniki_seq.txt", std::ofstream::trunc);

    for (unsigned b_method = 0; b_method < b_limit + 1; b_method++) {
        std::cout << b_method << std::endl;
        outfile << adorate_sequential(graph, b_method, old_values) << std::endl;
    }

    outfile.close();

    check_correctness();

    return 0;
}