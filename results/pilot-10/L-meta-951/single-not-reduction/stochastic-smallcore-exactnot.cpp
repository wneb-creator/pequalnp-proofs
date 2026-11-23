#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

constexpr int N=7, K=9, W=2, INPUTS=N+1, M=6;
using Table=std::array<std::uint64_t,W>;
struct Gate { int op,a,b; };
using Circuit=std::array<Gate,K>;
const std::vector<std::vector<int>> sets{{0,2},{0,3},{0,4,5,6},{1,4},{1,5},{1,2,3,6}};
std::array<Table,INPUTS> inputs{};
std::array<Table,M> targets{};
std::array<int,M> best_outputs{};
std::mt19937_64 rng(9512032);
int random_int(int n) { return int(rng()%n); }
int evaluate(const Circuit& c,std::array<int,M>* outputs=nullptr) {
    std::array<Table,INPUTS+K> wires{};
    std::copy(inputs.begin(),inputs.end(),wires.begin());
    int nots=0;
    for(int g=0;g<K;++g) {
        const auto &node=c[g];
        if(node.a<0||node.a>=INPUTS+g||node.b<0||node.b>=INPUTS+g) return 1000000;
        nots += node.op==2;
        if(nots>1) return 1000000;
        for(int w=0;w<W;++w) {
            auto a=wires[node.a][w],b=wires[node.b][w];
            wires[INPUTS+g][w]=node.op==0?(a&b):node.op==1?(a|b):node.op==2?~a:~std::uint64_t(0);
        }
    }
    int score=0;
    for(int t=0;t<M;++t) {
        int best=1000000,idx=-1;
        for(int g=0;g<INPUTS+K;++g) {
            int loss=0;
            for(int w=0;w<W;++w) {
                loss += 15*__builtin_popcountll(wires[g][w]&~targets[t][w]);
                loss += __builtin_popcountll(~wires[g][w]&targets[t][w]);
            }
            if(loss<best) {best=loss;idx=g;}
        }
        score+=best;
        if(outputs) (*outputs)[t]=idx;
    }
    return score;
}
Circuit seed() {
    std::array<int,M> order{}; std::iota(order.begin(),order.end(),0);
    std::shuffle(order.begin(),order.end(),rng);
    std::vector<Gate> full;
    for(int t:order) {
        auto s=sets[t];std::shuffle(s.begin(),s.end(),rng);
        int current=s[0];
        for(unsigned j=1;j<s.size();++j){
            full.push_back({1,current,s[j]});
            current=INPUTS+int(full.size())-1;
        }
    }
    int del=random_int(int(full.size())),replacement=full[del].a;
    auto remap=[&](int x) {if(x==INPUTS+del)return replacement;return x>INPUTS+del?x-1:x;};
    Circuit c{};int k=0;
    for(int j=0;j<int(full.size());++j)if(j!=del)c[k++]={full[j].op,remap(full[j].a),remap(full[j].b)};
    return c;
}
void dump(const Circuit &c,int score,const char* path) {
    std::ofstream out(path);
    std::array<int,M> outputs{};evaluate(c,&outputs);
    out<<"score "<<score<<"\n";
    for(int j=0;j<K;++j)out<<INPUTS+j<<" "<<c[j].op<<" "<<c[j].a<<" "<<c[j].b<<"\n";
    out<<"outputs";for(auto x:outputs)out<<" "<<x;out<<"\n";
}
int main(int argc,char**argv) {
    if(argc!=3){std::cerr<<"usage: stochastic seconds best-file\n";return 2;}
    int seconds=std::stoi(argv[1]);
    for(int x=0;x<(1<<N);++x) {
        for(int v=0;v<N;++v)if((x>>v)&1)inputs[v][x/64]|=1ull<<(x%64);
        for(int t=0;t<M;++t)for(int v:sets[t])if((x>>v)&1){targets[t][x/64]|=1ull<<(x%64);break;}
    }
    auto started=std::chrono::steady_clock::now();auto last=started;
    int global_best=1000000;Circuit best{};std::uint64_t steps=0,restarts=0;
    for(;;) {
        Circuit current=seed();current[random_int(K)].op=2;int score=evaluate(current);
        for(int step=0;step<10000;++step) {
            ++steps;
            auto candidate=current;int g=random_int(K),kind=random_int(10),limit=INPUTS+g;
            if(kind<4)candidate[g].a=random_int(limit);
            else if(kind<8)candidate[g].b=random_int(limit);
            else {
                int op=random_int(4);
                if(op==2)for(auto& x:candidate)if(x.op==2)x.op=random_int(2);
                candidate[g].op=op;
            }
            bool has_not=false;for(const auto& node:candidate)has_not|=node.op==2;
            if(!has_not)candidate[random_int(K)].op=2;
            int next=evaluate(candidate);
            double temp=40.0*std::pow(0.0125,double(step)/10000);
            bool accept=next<=score||std::generate_canonical<double,53>(rng)<std::exp(double(score-next)/temp);
            if(accept){current=candidate;score=next;}
            if(score<global_best) {
                global_best=score;best=current;dump(best,score,argv[2]);
                std::cout<<"best="<<score<<" steps="<<steps<<" restarts="<<restarts<<std::endl;
                if(score==0){std::cout<<"FOUND exact full-truth-table candidate\n";return 0;}
            }
            if(steps%1024==0) {
                auto now=std::chrono::steady_clock::now();
                double elapsed=std::chrono::duration<double>(now-started).count();
                if(std::chrono::duration<double>(now-last).count()>=30){std::cout<<"elapsed="<<elapsed<<" steps="<<steps<<" restarts="<<restarts<<" best="<<global_best<<std::endl;last=now;}
                if(elapsed>=seconds){std::cout<<"NO WITNESS; stochastic search is incomplete. elapsed="<<elapsed<<" steps="<<steps<<" restarts="<<restarts<<" best="<<global_best<<std::endl;return 1;}
            }
        }
        ++restarts;
    }
}
