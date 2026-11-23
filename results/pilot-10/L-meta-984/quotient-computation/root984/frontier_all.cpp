#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
struct U {
 __uint128_t lo=0,hi=0;
 U(uint64_t v=0):lo(v),hi(0){}
 U(__uint128_t a,__uint128_t b):lo(a),hi(b){}
 explicit operator bool()const{return lo||hi;}
 explicit operator uint64_t()const{return uint64_t(lo);}
 explicit operator unsigned()const{return unsigned(lo);}
 friend bool operator==(U a,U b){return a.lo==b.lo&&a.hi==b.hi;}
 friend bool operator<(U a,U b){return a.hi<b.hi||(a.hi==b.hi&&a.lo<b.lo);}
 friend U operator&(U a,U b){return U(a.lo&b.lo,a.hi&b.hi);}
 friend U operator|(U a,U b){return U(a.lo|b.lo,a.hi|b.hi);}
 friend U operator~(U a){return U(~a.lo,~a.hi);}
 friend U operator>>(U a,int s){if(s<=0)return a;if(s>=256)return U();if(s>=128)return U(a.hi>>(s-128),0);return U((a.lo>>s)|(a.hi<<(128-s)),a.hi>>s);}
 friend U operator<<(U a,int s){if(s<=0)return a;if(s>=256)return U();if(s>=128)return U(0,a.lo<<(s-128));return U(a.lo<<s,(a.hi<<s)|(a.lo>>(128-s)));}
 friend U operator-(U a,uint64_t b){return U(a.lo-b,a.hi-(a.lo<b));}
 U& operator|=(U b){lo|=b.lo;hi|=b.hi;return *this;}
 U& operator>>=(int s){*this=*this>>s;return *this;}
};
using State=std::vector<U>;
struct Hash {size_t operator()(State const& s)const {uint64_t h=0x9e3779b97f4a7c15ULL;for(U w:s){for(uint64_t x:{uint64_t(w),uint64_t(w>>64),uint64_t(w>>128),uint64_t(w>>192)}){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;x^=x>>31;h^=x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}}return h;}};
std::string hex(U w){if(!w)return "0";std::string s;while(w){s.push_back("0123456789abcdef"[unsigned(w&15)]);w>>=4;}std::reverse(s.begin(),s.end());return s;}
int main(int argc,char**argv){
 if(argc!=4){std::cerr<<"usage: frontier graphfile maxstates outputprefix\n";return 2;}
 int n,budget,m;std::ifstream input(argv[1]);input>>n>>budget>>m;if(!input||n<1||n>7||m<1)return 2;size_t limit=std::stoull(argv[2]);std::string prefix=argv[3];
 std::vector<std::pair<int,int>> edges;for(int i=0;i<m;i++){int a,b;input>>a>>b;if(!input||a<0||a>=n||b<0||b>=n)return 2;edges.push_back({a,b});}
 std::vector<int> neg;for(int x=0;x<(1<<n);x++){bool ok=true;for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1))ok=false;if(ok)neg.push_back(x);}
 std::vector<int> maximal;for(int x:neg){bool maximalx=true;for(int y:neg)if(x!=y&&(x&y)==x)maximalx=false;if(maximalx)maximal.push_back(x);}
 std::vector<std::pair<int,int>> rows;for(int x:maximal)for(auto[a,b]:edges)rows.push_back({x,(1<<a)|(1<<b)});
 int k=rows.size();if(2*k>256)return 3;U mask=(U(1)<<k)-1,goal=mask<<k;State initial;
 for(int v=0;v<n;v++){U w=0;for(int i=0;i<k;i++){w|=U(rows[i].first>>v&1)<<i;w|=U(rows[i].second>>v&1)<<(k+i);}initial.push_back(w);}std::sort(initial.begin(),initial.end());
 std::ofstream meta(prefix+".meta.json");meta<<"{\"k\":"<<k<<",\"budget\":"<<budget<<",\"negative_rows\":[";for(size_t i=0;i<rows.size();i++){if(i)meta<<',';meta<<rows[i].first;}meta<<"],\"positive_rows\":[";for(size_t i=0;i<rows.size();i++){if(i)meta<<',';meta<<rows[i].second;}meta<<"],\"inputs_hex\":[";for(size_t i=0;i<initial.size();i++){if(i)meta<<',';meta<<'"'<<hex(initial[i])<<'"';}meta<<"]}\n";meta.close();
 std::unordered_set<State,Hash> cur,next;cur.insert(initial);auto started=std::chrono::steady_clock::now();uint64_t candidates=0;
 auto covered=[&](State const&s){U c=0;for(U w:s)c|=(w>>k)&~w;return(c&mask)==mask;};
 for(int s=budget;s>=0;s--){
  double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();std::cout<<"remaining="<<s<<" states="<<cur.size()<<" candidates="<<candidates<<" seconds="<<sec<<std::endl;
  std::ofstream out(prefix+".layer"+std::to_string(s)+".jsonl");for(auto const&ws:cur){out<<'[';for(size_t j=0;j<ws.size();j++){if(j)out<<',';out<<'"'<<hex(ws[j])<<'"';}out<<"]\n";}out.close();
  if(s==0){bool sat=cur.count(State{goal});std::cout<<(sat?"SURVIVING_GOAL":"EXHAUSTED")<<std::endl;return sat?10:0;}
  next.clear();bool over=false;
  auto add=[&](State w){candidates++;if(w.size()>size_t(s)||!covered(w))return;std::sort(w.begin(),w.end());next.insert(std::move(w));if(next.size()>limit)over=true;};
  for(auto const&ws:cur){
   int width=ws.size(),slack=s+1-width;
   if(slack>=1)add(ws);
   for(int i=0;i<width;i++){
    if(slack>=2){State w=ws;w.push_back(ws[i]);add(std::move(w));}
    for(int j=i+1;j<width;j++)for(int op=0;op<2;op++)for(int keep=0;keep<4;keep++){
     int saves=(keep&1)+((keep>>1)&1);if(slack<saves)continue;State w;w.reserve(width+1);w.push_back(op?(ws[i]|ws[j]):(ws[i]&ws[j]));for(int l=0;l<width;l++)if(l!=i&&l!=j)w.push_back(ws[l]);if(keep&1)w.push_back(ws[i]);if(keep&2)w.push_back(ws[j]);add(std::move(w));
    }
   }
   if(over){std::cout<<"STATE_CAP remaining="<<s-1<<" partial_states="<<next.size()<<std::endl;return 11;}
   if(std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>180){std::cout<<"TIME_CAP remaining="<<s-1<<" partial_states="<<next.size()<<std::endl;return 12;}
  }
  cur.swap(next);
 }
}
