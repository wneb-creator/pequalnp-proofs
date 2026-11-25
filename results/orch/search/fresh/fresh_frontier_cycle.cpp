#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <tuple>
#include <unordered_map>
#include <vector>

using Word=uint64_t;
struct Wire {
    Word p,z;
    auto operator<=>(const Wire&) const=default;
};
struct StateHash {
    size_t operator()(const std::vector<Wire>& v) const noexcept {
        size_t h = v.size();
        for(auto a:v){
            h^=(a.p+0x9e3779b97f4a7c15ull+(h<<6)+(h>>2));
            h^=(a.z+0x9e3779b97f4a7c15ull+(h<<6)+(h>>2));
        }
        return h;
    }
};
struct Step { bool meet; Wire a,b,h; };
struct Solver {
    int n,p,z,cap,ng,seconds; Word allP,allZ;
    std::vector<Wire> start;
    std::vector<std::vector<int>> sym;
    std::unordered_map<std::vector<Wire>,int,StateHash> memo;
    std::vector<Step> path;
    uint64_t states=0,memosize=175000;
    std::chrono::steady_clock::time_point t0=std::chrono::steady_clock::now();
    double elapsed()const{return std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();}
    Solver(const char* filename,int delta,int time) : seconds(time) {
        std::ifstream f(filename);
        if(!(f>>n>>p>>z>>cap>>ng)||p>63||z>64||n>40)throw 2;
        cap+=delta;
        allP=(Word(1)<<p)-1;allZ=z==64?~Word(0):(Word(1)<<z)-1;
        for(int i=0;i<n;++i){Wire w;f>>w.p>>w.z;start.push_back(w);}
        for(int s=0;s<ng;++s){std::vector<int> per(n);for(auto& i:per)f>>i;sym.push_back(per);}
    }
    bool root_rep(int i,int j,int ka,int kb)const{
        auto key=std::tuple{i,j,ka,kb};
        for(auto &per:sym){
            int ii=per[i],jj=per[j],k1=ka,k2=kb;
            if(ii>jj){std::swap(ii,jj);std::swap(k1,k2);}
            if(std::tuple{ii,jj,k1,k2}<key)return false;
        }
        return true;
    }
    bool dfs(const std::vector<Wire>& live,int slack,int d){
        if(slack<0)return false;
        if(std::binary_search(live.begin(),live.end(),Wire{allP,allZ}))return true;
        int l=live.size();
        if(l<2)return false;
        if(auto it=memo.find(live);it!=memo.end() && it->second>=slack)return false;
        if((++states%16384)==0 && elapsed()>seconds)throw 1;
        if(memo.size()>memosize)memo.clear();
        std::array<Word,64> needP{},needZ{};
        for(int t=0;t<p;++t){
            Word used=0,multi=0,flag=Word(1)<<t;
            for(auto w:live)if(w.p&flag){multi|=used&w.z;used|=w.z;}
            if(used!=allZ)return false;
            Word singleton=allZ^multi;
            if(!singleton)continue;
            for(int j=0;j<l;++j)if((live[j].p&flag)&&(live[j].z&singleton)){
                needP[j]|=flag;needZ[j]|=live[j].z&singleton;
            }
        }
        if(slack <= 6){
            for(int t=0;t<p;++t){
                Word flag=Word(1)<<t;
                std::array<Word,8> seen{};
                for(int i=0;i<l;++i)if(needP[i]&flag){
                    Word carry=needZ[i];
                    for(int u=0;carry && u<=slack;++u){
                        Word old=seen[u];
                        seen[u]|=carry;
                        carry&=old;
                    }
                    if(carry)return false;
                }
            }
        }
        for(int spend=0;spend<=std::min(slack,2);++spend)
          for(int i=0;i<l;++i)for(int j=i+1;j<l;++j){
            Wire a=live[i],b=live[j];
            for(int meet=0;meet<2;++meet){
                Wire h=meet?Wire{a.p&b.p,a.z|b.z}:Wire{a.p|b.p,a.z&b.z};
                if(!h.p||!h.z||std::binary_search(live.begin(),live.end(),h))continue;
                bool needa=meet?(needP[i]&~b.p):(needZ[i]&~b.z);
                bool needb=meet?(needP[j]&~a.p):(needZ[j]&~a.z);
                if(needa+needb>spend)continue;
                for(int ka=needa;ka<=1;++ka){
                    int kb=spend-ka;
                    if(kb<needb || kb>1)continue;
                    if(!d&&!root_rep(i,j,ka,kb))continue;
                    std::vector<Wire> nw;
                    nw.reserve(l+1);
                    for(int u=0;u<l;++u)if((u!=i||ka) && (u!=j||kb))nw.push_back(live[u]);
                    nw.insert(std::lower_bound(nw.begin(),nw.end(),h),h);
                    path.push_back({bool(meet),a,b,h});
                    if(dfs(nw,slack-spend,d+1))return true;
                    path.pop_back();
                }
            }
        }
        auto [it,ins]=memo.try_emplace(live,slack);
        if(!ins)it->second=std::max(it->second,slack);
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    Solver s(argv[1],std::stoi(argv[2]),std::stoi(argv[3]));
    std::string status="UNKNOWN";
    try{status=s.dfs(s.start,s.cap-s.n+1,0)?"SAT":"UNSAT";}catch(int v){if(v!=1)throw;}
    std::cout<<"{\"instance\":\""<<argv[1]<<"\",\"gates\":"<<s.cap<<",\"status\":\""<<status<<"\",\"states\":"<<s.states<<",\"elapsed\":"<<s.elapsed()<<",\"path\":[";
    if(status=="SAT"){
      bool first=true;
      for(auto &g:s.path){
        if(!first)std::cout<<",";
        first=false;
        std::cout<<"[\""<<(g.meet?"&":"|")<<"\","<<g.a.p<<","<<g.a.z<<","<<g.b.p<<","<<g.b.z<<","<<g.h.p<<","<<g.h.z<<"]";
      }
    }
    std::cout<<"]}\n";
}
