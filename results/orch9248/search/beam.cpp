#include <algorithm>
#include <atomic>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>

using U = uint64_t;
const U EVEN = 0x5555555555ULL;
U neg(U x) { return ((x & EVEN) << 1) | ((x & (EVEN << 1)) >> 1); }
std::atomic<bool> stopped(false);
void stop(int) { stopped = true; }
struct Closure { U forced; bool conflict; };
Closure propagate(const std::vector<U>& db, U forced) {
    U falsified = neg(forced);
    bool changed;
    do {
        changed = false;
        for (U clause : db) {
            U remaining = clause & ~falsified;
            if (!remaining) return {forced,true};
            if (!(remaining & (remaining-1)) && !(remaining & forced)) {
                forced |= remaining;
                falsified |= neg(remaining);
                changed = true;
            }
        }
    } while (changed);
    return {forced,false};
}
std::vector<U> read(const std::string& name) {
    std::ifstream in(name);
    if (!in) throw std::runtime_error("cannot read input");
    std::vector<U> result;
    U x;
    while (in >> x) result.push_back(x);
    return result;
}
struct State { std::vector<U> learned; double value; unsigned hits[20]{}; };
std::string key(const std::vector<U>& learned) {
    auto v=learned;
    std::sort(v.begin(),v.end());
    std::string s;
    for (U x:v) s+=std::to_string(x)+",";
    return s;
}
void witness(const std::string& name,const std::vector<U>& clauses) {
    std::ofstream out(name);
    out << "{\"oldest_first_clauses\":[";
    for (size_t i=0;i<clauses.size();++i) {
        if (i) out << ',';
        out << '[';
        bool first=true;
        for (int j=0;j<40;++j) if ((clauses[i]>>j)&1) {
            if (!first) out << ',';
            first=false;out << j;
        }
        out << ']';
    }
    out << "],\"learned_count\":" << clauses.size() << "}\n";
}
int main(int argc,char** argv) {
    if (argc != 8) {
        std::cerr << "usage: beam seconds seed beam_width branch_count pool first_orbits output_json\n";
        return 2;
    }
    signal(SIGTERM,stop);signal(SIGINT,stop);
    const int seconds=std::stoi(argv[1]),width=std::stoi(argv[3]),branches=std::stoi(argv[4]);
    std::mt19937_64 random(std::stoull(argv[2]));
    const auto start=std::chrono::steady_clock::now();
    auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
    auto pool=read(argv[5]),first=read(argv[6]);
    std::vector<U> base;
    for (int p=0;p<5;++p) {U c=0;for(int h=0;h<4;++h)c|=1ULL<<(2*(4*p+h));base.push_back(c);}
    for(int h=0;h<4;++h)for(int p=0;p<5;++p)for(int q=p+1;q<5;++q)
        base.push_back((1ULL<<(2*(4*p+h)+1))|(1ULL<<(2*(4*q+h)+1)));
    U fixed[20]{};
    for (int p=0;p<5;++p) for(int h=0;h<4;++h) {
        U f=1ULL<<(2*(4*p+h));
        for(int j=0;j<4;++j)if(j!=h)f|=1ULL<<(2*(4*p+j)+1);
        for(int i=0;i<5;++i)if(i!=p)f|=1ULL<<(2*(4*i+h)+1);
        fixed[4*p+h]=f;
    }
    std::vector<U> probes{0};
    for(U c:pool)if(__builtin_popcountll(c)<=3)probes.push_back(c);
    std::vector<double> weight;
    for(U c:probes) {int w=__builtin_popcountll(c);weight.push_back(w==0?10000000.0:w==1?100000.0:w==2?500.0:1.0);}
    uint64_t nodes=0,actions=0,restarts=0;
    size_t best_complete=21;
    while (!stopped && elapsed()<seconds) {
        ++restarts;
        std::vector<State> beam(1);
        for(int depth=0;depth<11 && !stopped && elapsed()<seconds;++depth) {
            std::vector<State> next;
            std::unordered_set<std::string> seen;
            for(const State& state:beam) {
                if(stopped || elapsed()>=seconds)break;
                ++nodes;
                auto db=base;db.insert(db.end(),state.learned.begin(),state.learned.end());
                std::vector<Closure> closures;
                double current=0;
                for(size_t j=0;j<probes.size();++j) {
                    auto r=propagate(db,neg(probes[j]));closures.push_back(r);
                    current+=r.conflict?weight[j]:0.002*__builtin_popcountll(r.forced);
                }
                if(closures[0].conflict) {
                    auto learned=state.learned;learned.push_back(0);witness(argv[7],learned);
                    std::cout << "FOUND count=" << learned.size() << " seconds=" << elapsed() << std::endl;return 0;
                }
                // Complete promising partial states with currently RUP unit clauses.
                // This produces useful independently checkable upper-bound traces
                // even if they remain longer than the target twelve.
                if(depth>=4) {
                    auto trial=state.learned;
                    auto complete=db;
                    bool contradiction=false;
                    while(trial.size()<best_complete-1) {
                        auto current_closure=propagate(complete,0);
                        if(current_closure.conflict) {contradiction=true;break;}
                        bool added=false;
                        for(int l=0;l<40;++l) {
                            U unit=1ULL<<l;
                            if(current_closure.forced & unit)continue;
                            if(std::find(complete.begin(),complete.end(),unit)!=complete.end())continue;
                            if(propagate(complete,neg(unit)).conflict) {
                                complete.push_back(unit);trial.push_back(unit);added=true;break;
                            }
                        }
                        if(!added)break;
                    }
                    contradiction=contradiction||propagate(complete,0).conflict;
                    if(contradiction) {
                        trial.push_back(0);
                        // Delete a step only after replaying every remaining RUP step.
                        for(size_t k=0;k+1<trial.size();) {
                            auto reduced=trial;reduced.erase(reduced.begin()+k);
                            auto test=base;bool valid=true;
                            for(U cl:reduced) {
                                if(!propagate(test,neg(cl)).conflict){valid=false;break;}
                                test.push_back(cl);
                            }
                            if(valid)trial=std::move(reduced);else ++k;
                        }
                        if(trial.size()<best_complete) {
                            best_complete=trial.size();witness(argv[7],trial);
                            std::cout << "BEST_COMPLETE count=" << best_complete << " seconds=" << elapsed() << std::endl;
                            if(best_complete<=12)return 0;
                        }
                    }
                }
                struct Action {U clause;double score;};
                std::vector<Action> choices;
                const auto& options=depth==0?first:pool;
                for(U clause:options) {
                    if(stopped || elapsed()>=seconds)break;
                    bool skip=false;
                    for(int q=0;q<20;++q)if((clause&fixed[q])&&state.hits[q]>=7){skip=true;break;}
                    if(skip)continue;
                    for(U old:db)if((old&clause)==old){skip=true;break;}
                    if(skip || !propagate(db,neg(clause)).conflict)continue;
                    ++actions;
                    auto ext=db;ext.push_back(clause);
                    double score=current;
                    for(size_t j=0;j<probes.size();++j) {
                        if(closures[j].conflict)continue;
                        U rem=clause & ~neg(closures[j].forced);
                        if(rem && (rem&(rem-1)))continue;
                        auto r=propagate(ext,closures[j].forced);
                        if(r.conflict)score+=weight[j]-0.002*__builtin_popcountll(closures[j].forced);
                        else score+=0.002*(__builtin_popcountll(r.forced)-__builtin_popcountll(closures[j].forced));
                    }
                    if(propagate(ext,0).conflict) {
                        auto learned=state.learned;learned.push_back(clause);learned.push_back(0);
                        witness(argv[7],learned);
                        std::cout << "FOUND count=" << learned.size() << " seconds=" << elapsed() << std::endl;return 0;
                    }
                    // Randomized tie-breaking explores differently at each restart.
                    score+=std::generate_canonical<double,53>(random)*(10.0+2.0*restarts);
                    choices.push_back({clause,score});
                }
                std::sort(choices.begin(),choices.end(),[](auto a,auto b){return a.score>b.score;});
                const size_t keep=std::min(choices.size(),size_t(branches));
                for(size_t j=0;j<keep;++j) {
                    State child=state;child.learned.push_back(choices[j].clause);child.value=choices[j].score;
                    if(!seen.insert(key(child.learned)).second)continue;
                    for(int q=0;q<20;++q)if(choices[j].clause&fixed[q])++child.hits[q];
                    next.push_back(std::move(child));
                }
            }
            std::sort(next.begin(),next.end(),[](const auto&a,const auto&b){return a.value>b.value;});
            if(next.size()>size_t(width))next.resize(width);
            beam=std::move(next);
            std::cout << "PROGRESS restart=" << restarts << " depth=" << depth+1 << " states=" << beam.size()
                      << " nodes=" << nodes << " actions=" << actions << " seconds=" << elapsed()
                      << " best=" << (beam.empty()?0:beam[0].value) << std::endl;
            if(beam.empty())break;
        }
    }
    std::cout << "NO_WITNESS seconds=" << elapsed() << " nodes=" << nodes << " actions=" << actions
              << " stopped=" << stopped << std::endl;
    return 0;
}
