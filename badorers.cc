#include <unordered_set>
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
using ud_graph = std::map<unsigned, vector_puu>;
using std_graph = std::vector<std::pair<unsigned, std::vector<pair_uu >>>;
using u_queue = std::queue<unsigned, std::list<unsigned>>;
using set_u_desc = std::set<unsigned, std::greater<>>;
using set_puu_desc = std::set<pair_uu, std::greater<>>;

namespace bar {
    class barrier {
    private:
        int count_;
        int i_;
        std::condition_variable cv;
        std::mutex cv_mutex;
        std::mutex lock;
        bool finish;

        void action(u_queue& Q, set_u_desc& R, std::vector<unsigned>& B,
                    std::vector<unsigned>& DB) {
            for (auto& r : R) {
                Q.push(r);
            }
            R = set_u_desc();
            for (int i = 0; i < B.size(); ++i) {
                B[i] = DB[i];
                DB[i] = 0;
            }
            finish = Q.empty();
        }

    public:
        explicit barrier(int count)
                : count_(count), i_(0), finish(false) {}

        void await(u_queue& Q, set_u_desc& R, std::vector<unsigned>& B,
                   std::vector<unsigned>& DB) {

            std::unique_lock<std::mutex> lck(lock);
            if (i_ < count_) {
                i_++;
            }
            if (i_ >= count_) {
                std::lock_guard<std::mutex> rstl(cv_mutex);
                lck.unlock();i_ = 0;

                action(Q, R, B, DB);

                cv.notify_all();
                return;
            } else {
                cv.wait(lck);
            }
            lck.unlock();
        }

        bool finished() {
            return finish;
        }
    };
}


unsigned count_edges_parall(std::vector<set_puu_desc>& S) {
    unsigned result{0};
    for (int i = 0; i < S.size(); ++i) {
        for (auto &pair : S[i]) {
            auto &s_x = S[pair.second];
            if (s_x.count({pair.first, i})) {
                result += pair.first;
                s_x.erase({pair.first, i});
            }
        }
    }
    return result;
}

int get_elem(u_queue& Q, std::mutex& mutex_Q) {
    int u = -1;
    mutex_Q.lock();
    if (!Q.empty()) {
        u = Q.front();
        Q.pop();
    }
    mutex_Q.unlock();
    return u;
}

pair_uu find_neighbour(std::vector<set_puu_desc>& N,
                       std::vector<set_puu_desc>& S,
                       std::vector<std::unique_ptr<std::mutex>>& mutexes,
                       std::vector<unsigned>& old_values,
                       unsigned method, unsigned u) {
    for (const auto &neighbour : N[u]) {
        std::unique_lock<std::mutex> neighbour_sm(*mutexes[neighbour.second]);
        const auto& s_last = S[neighbour.second].rbegin();
        auto& s_x = S[neighbour.second];
        if (bvalue(method, old_values[neighbour.second]) == 0) {
            continue;
        }
        if (s_x.size() < bvalue(method, old_values[neighbour.second]) ||
                !((neighbour.first < s_last->first) ||
                 (neighbour.first == s_last->first && u < s_last->second))) {
            return std::make_pair(neighbour.first, neighbour.second);
        } else {
            continue;
        }
    }
    return {0, 0};
}

void adorate_parallel(u_queue& Q,
                      set_u_desc& R,
                      std::vector<set_puu_desc>& S,
                      std::vector<set_puu_desc>& N,
                      std::vector<unsigned>& B,
                      std::vector<unsigned>& DB,
                      std::vector<std::unique_ptr<std::mutex>>& mutexes,
                      std::mutex& mutex_Q,
                      std::mutex& mutex_R,
                      unsigned method,
                      std::vector<bool>& N_exhausted,
                      bar::barrier &barrier,
                      std::vector<unsigned>& old_values) {
    pair_uu p;
    int a;
    while (!barrier.finished()) {
        a = get_elem(Q, mutex_Q);
        while (a != -1) {
            auto u = (unsigned) a;
            unsigned j = 1;

            while (j <= B[u] && !N_exhausted[u]) {
                p = find_neighbour(N, S, mutexes, old_values, method, u);

                if (p.first == 0) {
                    N_exhausted[u] = true;
                    continue;
                }

                std::unique_lock<std::mutex> mut_s(*mutexes[p.second]);

                auto & s_x = S[p.second];
                const auto& s_last = s_x.rbegin();

                if (s_x.size() == bvalue(method, old_values[p.second]) &&
                        (p.first < s_last->first ||
                        (p.first == s_last->first && u < s_last->second))) {
                    mut_s.unlock();
                    continue;
                }

                if (s_x.size() == bvalue(method, old_values[p.second])) {
                    pair_uu y(*s_last);
                    s_x.erase(*s_last);

                    std::unique_lock<std::mutex> mut_t_y(*mutexes[y.second]);
                    DB[y.second]++;
                    mut_t_y.unlock();

                    mutex_R.lock();
                    R.insert(y.second);
                    mutex_R.unlock();
                }

                j++;
                s_x.insert(std::make_pair(p.first, u));

                mut_s.unlock();

                N[u].erase(p);
            }
            a = get_elem(Q, mutex_Q);
        }

        barrier.await(Q, R, B, DB); //Q = R; R = u_queue(); B = DB; DB = new map;

    }
}

void write_info(u_queue& Q, std::vector<set_puu_desc>& S,
                std::vector<set_puu_desc>& N,
                std::vector<unsigned>& B,
                std::vector<unsigned>& DB,
                std::vector<std::unique_ptr<std::mutex>>& S_mutex,
                const std_graph& graph,
                std::vector<unsigned>& old_values,
                unsigned b_u,
                std::vector<bool>& N_exhausted) {

    for (const auto &vertex : graph) {
        B.push_back(bvalue(b_u, old_values[vertex.first]));
        DB.push_back(0);
        S.emplace_back(set_puu_desc());
        N.emplace_back(set_puu_desc());
        S_mutex.emplace_back(std::make_unique<std::mutex>());
        N_exhausted.emplace_back(false);
        auto& n_set = N.at(vertex.first);

        for (const auto &edge : vertex.second) {
            n_set.insert(std::make_pair(edge.second, edge.first));
        }
    }

    for (auto i = (long) (graph.size() - 1); i >= 0; --i) {
        Q.push(graph[i].first);
    }
}

unsigned b_suitor_parallel(std_graph &graph, std::vector<unsigned>& old_values,
                           unsigned thread_num, unsigned b_u) {
    std::vector<std::thread> threads;
    u_queue Q;
    set_u_desc R;
    std::vector<set_puu_desc> S, N;
    std::vector<unsigned> B, DB;
    std::vector<std::unique_ptr<std::mutex>> mutexes;
    std::vector<bool> N_exhausted;
    std::mutex mutex_Q, mutex_R;
    bar::barrier barrier(thread_num);

    write_info(Q, S, N, B, DB, mutexes, graph, old_values, b_u, N_exhausted);

    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();

    for (unsigned i = 0; i < thread_num; ++i) {
        threads.emplace_back(adorate_parallel, std::ref(Q), std::ref(R),
                             std::ref(S), std::ref(N), std::ref(B),
                             std::ref(DB), std::ref(mutexes),
                             std::ref(mutex_Q), std::ref(mutex_R), b_u,
                             std::ref(N_exhausted), std::ref(barrier),
                             std::ref(old_values));
    }

    for (std::thread &t: threads) {
        t.join();
    }
    std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
    unsigned result = count_edges_parall(S);
    std::cout << "Time : " << std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count() <<std::endl;
    return result;
}


void read_input(std_graph &graph_vec, std::vector<unsigned>& old_values,
                const std::string &file_name) {
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

            graph_map.insert(std::make_pair(node1,
                                 std::vector<std::pair<unsigned, unsigned>>()));
            graph_map.insert(std::make_pair(node2,
                                 std::vector<std::pair<unsigned, unsigned>>()));
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
    wyniki.open("../data/wyniki_parall.txt");
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

int main(int argc, const char * argv[]) {
    if (argc != 4)
        std::exit(1);

    unsigned thread_number = (unsigned) std::stoi(argv[1]);
    std::string file_name = argv[2];
    unsigned b_limit =  (unsigned) std::stoul(argv[3]);

    std_graph graph;
    std::vector<unsigned> old_values;

    read_input(graph, old_values, file_name);

    std::ofstream outfile ("../data/wyniki_parall.txt", std::ofstream::trunc);

    for (unsigned b_method = 0; b_method < b_limit + 1; b_method++) {
        std::cout << b_method << std::endl;
        outfile << b_suitor_parallel(graph, old_values,
                                     thread_number, b_method) << std::endl;
    }

    outfile.close();

    check_correctness();

    return 0;
}