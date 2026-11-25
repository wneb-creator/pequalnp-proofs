#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>

struct Gate { int op,a,b; };
using Circuit=std::array<Gate,63>;
using Table=std::array<uint64_t,4>;
std::array<Table,90> wire;
Table target;
std::vector<std::pair<unsigned,int>> rows;
std::vector<std::pair<int,int>> edges;
std::mt19937_64 rng;
int N,K,S,R,M,words;
bool forceReread;

std::pair<int,int> evaluate(const Circuit &c) {
    for(int i=0;i<S;i++)for(int k=0;k<words;k++)
        wire[N+i][k]=c[i].op?(wire[c[i].a][k]|wire[c[i].b][k]):(wire[c[i].a][k]&wire[c[i].b][k]);
    int fn=0,fp=0;
    for(int k=0;k<words;k++) {
        fn+=std::popcount(target[k]&~wire[N+S-1][k]);
        fp+=std::popcount(wire[N+S-1][k]&~target[k]);
    }
    return {fn,fp};
}
int badReads(const Circuit &c) {
    uint32_t shadow[90]={};uint64_t cover[90]={};
    for(int i=0;i<N;i++)shadow[i]=1u<<i;
    for(int i=0;i<S;i++) {
        int w=N+i,a=c[i].a,b=c[i].b;
        if(c[i].op){shadow[w]=shadow[a]|shadow[b];cover[w]=cover[a]|cover[b];}
        else for(unsigned j=0;j<edges.size();j++) {
            auto [p,l]=edges[j];
            if((((shadow[a]>>p)&1)&&((shadow[b]>>l)&1))||(((shadow[b]>>p)&1)&&((shadow[a]>>l)&1)))cover[w]|=1ull<<j;
        }
    }
    return std::popcount(wire[N+S-1][0]&((1ull<<M)-1)&~cover[N+S-1]);
}
bool save(const Circuit &c,uint64_t it,const std::string &path) {
    auto [fn,fp]=evaluate(c);std::string tmp=path+".new";std::ofstream f(tmp);
    f<<"errors "<<fn+fp<<" false_negative "<<fn<<" false_positive "<<fp<<" iteration "<<it<<" read1_missing "<<badReads(c)<<"\n";
    for(int i=0;i<S;i++)f<<N+i<<" "<<(c[i].op?"or":"and")<<" "<<c[i].a<<" "<<c[i].b<<"\n";
    f<<"error_masks:";for(int i=0;i<R;i++)if(((wire[N+S-1][i/64]>>(i%64))&1)!=unsigned(rows[i].second))f<<" "<<rows[i].first;
    f<<"\n";f.flush();if(!f.good())return false;f.close();return std::rename(tmp.c_str(),path.c_str())==0;
}
Circuit initial() {
    std::vector<Gate> g;std::vector<int> adj[26],stars,out;
    for(auto [a,b]:edges)adj[a].push_back(b);
    for(int i=0;i<K;i++){if(adj[i].size()!=4)std::abort();stars.push_back(i);}
    std::shuffle(stars.begin(),stars.end(),rng);
    auto combine=[&](std::vector<int> p) {
        while(p.size()>1) {
            std::shuffle(p.begin(),p.end(),rng);int a=p.back();p.pop_back();int b=p.back();p.pop_back();
            g.push_back({1,a,b});p.push_back(N-1+g.size());
        }
        return p[0];
    };
    int repeat=stars[rng()%stars.size()];
    for(int p:stars) {
        if(forceReread&&p==repeat) {
            std::shuffle(adj[p].begin(),adj[p].end(),rng);g.push_back({1,adj[p][0],adj[p][1]});
            int pair=N-1+g.size();
            if(rng()%2){g.push_back({0,p,p});int u=N-1+g.size();g.push_back({0,u,pair});}
            else{g.push_back({0,p,pair});int u=N-1+g.size();g.push_back({0,p,u});}
        }else{int u=combine(adj[p]);g.push_back({0,p,u});}
        out.push_back(N-1+g.size());
    }
    combine(out);Circuit c={};
    if(forceReread){if(int(g.size())!=S)std::abort();std::copy(g.begin(),g.end(),c.begin());return c;}
    if(int(g.size())!=S+1)std::abort();
    std::vector<int> removable;for(int i=0;i<4*K;i++)if(g[i].op&&(g[i].a<N||g[i].b<N))removable.push_back(i);
    int gone=removable[rng()%removable.size()],subst=g[gone].a<N?g[gone].b:g[gone].a;
    if(g[gone].a<N&&g[gone].b<N&&rng()%2)subst=g[gone].a;
    auto ref=[&](int v){if(v==N+gone)v=subst;if(v>N+gone)v--;return v;};
    for(int i=0,j=0;i<S+1;i++)if(i!=gone)c[j++]={g[i].op,ref(g[i].a),ref(g[i].b)};
    return c;
}
void mutate(Circuit &c) {
    int count=1+(rng()%100<8)+(rng()%100<2)*2;
    while(count--){int i=rng()%S,f=rng()%3;if(f==0)c[i].op^=1;else if(f==1)c[i].a=rng()%(N+i);else c[i].b=rng()%(N+i);}
}
int main(int argc,char**argv) {
    if(argc<5)return 2;
    std::ifstream data(argv[1]);data>>N>>K>>M>>R;S=5*K-2;words=(R+63)/64;
    if(N>26||K<2||S>63||R>256||M!=4*K||M>=64||!data)return 2;
    for(int i=0;i<M;i++){int a,b;data>>a>>b;if(a<0||a>=K||b<K||b>=N)return 2;edges.emplace_back(a,b);}
    for(int i=0;i<R;i++) {
        unsigned mask;int bit;data>>mask>>bit;if(!data)return 2;rows.emplace_back(mask,bit);
        for(int j=0;j<N;j++)if((mask>>j)&1)wire[j][i/64]|=1ull<<(i%64);
        if(bit)target[i/64]|=1ull<<(i%64);
    }
    int seconds=std::stoi(argv[2]);rng.seed(std::stoul(argv[3]));std::string path=argv[4];forceReread=argc>5&&std::stoi(argv[5]);
    Circuit current=initial(),bestCircuit=current;auto [a,b]=evaluate(current);
    if(b||a!=(forceReread?2:1)||(forceReread&&badReads(current)!=2))std::abort();
    int weight=1,score=a+b,best=score,localBest=score;
    uint64_t it=0,age=0,restarts=0;save(current,it,path);
    auto started=std::chrono::steady_clock::now(),next=started;
    while(std::chrono::steady_clock::now()-started<std::chrono::seconds(seconds)) {
        Circuit trial=current;mutate(trial);auto [fn,fp]=evaluate(trial);
        bool valid=!forceReread||badReads(trial)>0;int val=valid?weight*fn+fp:1000000;it++;age++;
        bool accept=val<=score;if(!accept&&val<score+4&&rng()%1000==0)accept=true;
        if(accept){current=trial;if(val<localBest){localBest=val;age=0;}score=val;}
        if(valid&&fn+fp<best){best=fn+fp;bestCircuit=trial;bool saved=save(trial,it,path);std::cout<<"best "<<best<<" iteration "<<it<<" restarts "<<restarts<<std::endl;if(best==0&&saved)return 0;}
        if(age>100000){current=initial();auto [u,v]=evaluate(current);weight=rng()%3==0?8:1;score=weight*u+v;localBest=score;age=0;restarts++;}
        auto now=std::chrono::steady_clock::now();if(now>=next){std::cout.clear();bool saved=save(bestCircuit,it,path);std::cout<<"elapsed "<<std::chrono::duration_cast<std::chrono::seconds>(now-started).count()<<" iteration "<<it<<" best "<<best<<" current "<<score<<" restarts "<<restarts<<std::endl;if(best==0&&saved)return 0;next=now+std::chrono::seconds(30);}
    }
    save(bestCircuit,it,path);std::cout<<"DONE no witness; best "<<best<<" proposals "<<it<<" restarts "<<restarts<<std::endl;return 1;
}
