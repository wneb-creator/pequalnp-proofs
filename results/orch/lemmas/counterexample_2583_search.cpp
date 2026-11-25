#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

struct Gate { int op,a,b; };
using Circuit=std::array<Gate,63>;
using Table=std::array<uint64_t,12>;
std::array<Table,89> wire;
Table target;
std::vector<std::pair<uint64_t,int>> rows;
std::vector<std::pair<int,int>> edges;
std::mt19937_64 rng;

std::pair<int,int> evaluate(const Circuit &c) {
    for(int i=0;i<63;i++)for(int k=0;k<12;k++)
        wire[26+i][k]=c[i].op?(wire[c[i].a][k]|wire[c[i].b][k]):(wire[c[i].a][k]&wire[c[i].b][k]);
    int fn=0,fp=0;
    for(int k=0;k<12;k++) {
        fn+=std::popcount(target[k]&~wire[88][k]);
        fp+=std::popcount(wire[88][k]&~target[k]);
    }
    return {fn,fp};
}

bool save(const Circuit &c,int iteration,const std::string &path) {
    auto [fn,fp]=evaluate(c);
    std::string tmp=path+".new";std::ofstream f(tmp);
    f<<"errors "<<(fn+fp)<<" false_negative "<<fn<<" false_positive "<<fp<<" iteration "<<iteration<<"\n";
    for(int i=0;i<63;i++)f<<(26+i)<<" "<<(c[i].op?"or":"and")<<" "<<c[i].a<<" "<<c[i].b<<"\n";
    f<<"error_masks:";
    for(unsigned i=0;i<rows.size();i++)if(((wire[88][i/64]>>(i%64))&1)!=unsigned(rows[i].second))f<<" "<<rows[i].first;
    f<<"\n";f.flush();if(!f.good())return false;f.close();
    return std::rename(tmp.c_str(),path.c_str())==0;
}

Circuit initial() {
    std::vector<Gate> init;
    std::vector<int> stars,out,adj[26];
    int side=rng()%2;
    for(auto [a,b]:edges) {if(side)std::swap(a,b);adj[a].push_back(b);}
    for(int v=0;v<26;v++)if(!adj[v].empty())stars.push_back(v);
    std::shuffle(stars.begin(),stars.end(),rng);
    auto combine=[&](std::vector<int> pool) {
        while(pool.size()>1) {
            std::shuffle(pool.begin(),pool.end(),rng);
            int a=pool.back();pool.pop_back();int b=pool.back();pool.pop_back();
            init.push_back({1,a,b});pool.push_back(25+init.size());
        }
        return pool[0];
    };
    for(int v:stars){int u=combine(adj[v]);init.push_back({0,v,u});out.push_back(25+init.size());}
    combine(out);if(init.size()!=64)std::abort();
    std::vector<int> removable;
    for(int i=0;i<52;i++)if(init[i].op&&(init[i].a<26||init[i].b<26))removable.push_back(i);
    int gone=removable[rng()%removable.size()];
    int subst=init[gone].a<26?init[gone].b:init[gone].a;
    if(init[gone].a<26&&init[gone].b<26&&rng()%2)subst=init[gone].a;
    auto remap=[&](int x){if(x==26+gone)x=subst;if(x>26+gone)x--;return x;};
    Circuit c;
    for(int i=0,j=0;i<64;i++)if(i!=gone)c[j++]={init[i].op,remap(init[i].a),remap(init[i].b)};
    return c;
}

void mutate(Circuit &c) {
    int count=1+(rng()%100<8)+(rng()%100<2)*2;
    while(count--) {
        int i=rng()%63,field=rng()%3;
        if(field==0)c[i].op^=1;
        else if(field==1)c[i].a=rng()%(26+i);
        else c[i].b=rng()%(26+i);
    }
}

int main(int argc,char**argv) {
    if(argc<5)return 2;
    std::ifstream data(argv[1]);int n,s,r,e;data>>n>>s>>r>>e;
    if(n!=26||s!=63||r!=756||e!=52)return 2;
    for(int i=0;i<r;i++) {
        uint64_t mask;int bit;data>>mask>>bit;if(!data)return 2;
        rows.emplace_back(mask,bit);
        for(int j=0;j<n;j++)if((mask>>j)&1)wire[j][i/64]|=1ull<<(i%64);
        if(bit)target[i/64]|=1ull<<(i%64);
        if(i<e){int a=std::countr_zero(mask);mask&=mask-1;int b=std::countr_zero(mask);edges.emplace_back(a,b);}
    }
    int seconds=std::stoi(argv[2]);rng.seed(std::stoul(argv[3]));std::string path=argv[4];
    Circuit current=initial(),bestCircuit=current;
    auto [fn,fp]=evaluate(current);int weight=1,score=fn+fp,best=score,it=0,stagnant=0,restarts=0,localBest=score;
    bool savedFpOne=false;
    save(current,it,path);
    auto started=std::chrono::steady_clock::now(),next=started;
    while(std::chrono::steady_clock::now()-started<std::chrono::seconds(seconds)) {
        Circuit trial=current;mutate(trial);
        auto [a,b]=evaluate(trial);int val=weight*a+b;it++;stagnant++;
        bool accept=val<=score;
        if(!accept&&val<score+4&&rng()%1000==0)accept=true;
        if(accept){current=trial;if(val<localBest){stagnant=0;localBest=val;}score=val;}
        if(a==0&&b==1&&!savedFpOne) {
            savedFpOne=save(trial,it,path+".one-false-positive");
            std::cout<<"one false positive, no false negatives at "<<it<<std::endl;
        }
        if(a+b<best) {
            best=a+b;bestCircuit=trial;bool saved=save(trial,it,path);
            std::cout<<"best "<<best<<" fn "<<a<<" fp "<<b<<" iteration "<<it<<" restarts "<<restarts<<std::endl;
            if(best==0&&saved)return 0;
        }
        if(stagnant>100000) {
            current=initial();auto [u,v]=evaluate(current);weight=(rng()%3==0?8:1);score=weight*u+v;localBest=score;stagnant=0;restarts++;
        }
        auto now=std::chrono::steady_clock::now();
        if(now>=next) {
            std::cout.clear();bool saved=save(bestCircuit,it,path);
            std::cout<<"elapsed "<<std::chrono::duration_cast<std::chrono::seconds>(now-started).count()<<" iteration "<<it<<" best "<<best<<" current "<<score<<" restarts "<<restarts<<std::endl;
            if(best==0&&saved)return 0;
            next=now+std::chrono::seconds(30);
        }
    }
    save(bestCircuit,it,path);
    std::cout<<"DONE no exact witness; best "<<best<<" proposals "<<it<<" restarts "<<restarts<<std::endl;
    return 1;
}
