#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <map>
#include <numeric>
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

struct UHash {size_t operator()(U w)const {uint64_t h=0x9e3779b97f4a7c15ULL;for(uint64_t x:{uint64_t(w),uint64_t(w>>64),uint64_t(w>>128),uint64_t(w>>192)}){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;x^=x>>31;h^=x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}return h;}};
struct Parent {size_t parent=0;int kind=0,a=0,b=0,op=0,keep=0,aut=0;};
int main(int argc,char**argv){
 if(argc!=5){std::cerr<<"usage: frontier_quotient graphfile maxstates outputprefix scorefile\n";return 2;}
 int n,budget,m;std::ifstream input(argv[1]);input>>n>>budget>>m;if(!input||n<1||n>7||m<1)return 2;size_t limit=std::stoull(argv[2]);std::string prefix=argv[3];
 std::vector<std::pair<int,int>> edges;bool adj[7][7]={};for(int i=0;i<m;i++){int a,b;input>>a>>b;if(!input||a<0||a>=n||b<0||b>=n||a==b)return 2;edges.push_back({a,b});adj[a][b]=adj[b][a]=true;}
 std::vector<uint64_t> codes;{std::ifstream scores(argv[4]);uint64_t c;while(scores>>c)codes.push_back(c);if(!scores.eof())return 4;}
 std::vector<int> neg;for(int x=0;x<(1<<n);x++){bool ok=true;for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1))ok=false;if(ok)neg.push_back(x);}
 std::vector<int> maximal;for(int x:neg){bool maximalx=true;for(int y:neg)if(x!=y&&(x&y)==x)maximalx=false;if(maximalx)maximal.push_back(x);}
 std::vector<std::pair<int,int>> rows;for(int x:maximal)for(auto[a,b]:edges)rows.push_back({x,(1<<a)|(1<<b)});
 int k=rows.size();if(2*k>256)return 3;U mask=(U(1)<<k)-1,goal=mask<<k;State initial;
 for(int v=0;v<n;v++){U w=0;for(int i=0;i<k;i++){w|=U(rows[i].first>>v&1)<<i;w|=U(rows[i].second>>v&1)<<(k+i);}initial.push_back(w);}std::sort(initial.begin(),initial.end());
 std::map<std::pair<int,int>,int> rowIndex;for(int i=0;i<k;i++)if(!rowIndex.emplace(rows[i],i).second)return 5;
 std::vector<std::vector<int>> vertexPerms,rowPerms,rowInversePerms;std::vector<int> p(n);std::iota(p.begin(),p.end(),0);
 do {bool ok=true;for(int a=0;a<n;a++)for(int b=0;b<n;b++)if(adj[a][b]!=adj[p[a]][p[b]])ok=false;if(!ok)continue;
  auto moveMask=[&](int x){int z=0;for(int v=0;v<n;v++)if(x>>v&1)z|=1<<p[v];return z;};
  std::vector<int> rp(k),inverse(k,-1);for(int i=0;i<k;i++){auto found=rowIndex.find({moveMask(rows[i].first),moveMask(rows[i].second)});if(found==rowIndex.end())return 6;rp[i]=found->second;if(inverse[rp[i]]!=-1)return 7;inverse[rp[i]]=i;}
  vertexPerms.push_back(p);rowPerms.push_back(rp);rowInversePerms.push_back(inverse);
 }while(std::next_permutation(p.begin(),p.end()));
 if(vertexPerms.empty())return 8;
 std::unordered_map<U,std::vector<U>,UHash> transformed;transformed.reserve(8192);
 auto transforms=[&](U w)->std::vector<U> const& {auto hit=transformed.find(w);if(hit!=transformed.end())return hit->second;std::vector<U> images;images.reserve(rowPerms.size());for(auto const&rp:rowPerms){U z=0;for(int i=0;i<k;i++){if(bool((w>>i)&U(1)))z|=U(1)<<rp[i];if(bool((w>>(k+i))&U(1)))z|=U(1)<<(k+rp[i]);}images.push_back(z);}return transformed.emplace(w,std::move(images)).first->second;};
 auto orient=[&](State ws){std::sort(ws.begin(),ws.end());State best=ws;int which=0;std::vector<std::vector<U> const*> images;images.reserve(ws.size());for(U w:ws)images.push_back(&transforms(w));for(size_t a=1;a<rowPerms.size();a++){State candidate;candidate.reserve(ws.size());for(auto image:images)candidate.push_back((*image)[a]);std::sort(candidate.begin(),candidate.end());if(std::lexicographical_compare(candidate.begin(),candidate.end(),best.begin(),best.end())){best=std::move(candidate);which=a;}}return std::make_pair(std::move(best),which);};
 auto initialOriented=orient(initial);initial=std::move(initialOriented.first);
 std::ofstream meta(prefix+".meta.json");meta<<"{\"k\":"<<k<<",\"budget\":"<<budget<<",\"negative_rows\":[";for(size_t i=0;i<rows.size();i++){if(i)meta<<',';meta<<rows[i].first;}meta<<"],\"positive_rows\":[";for(size_t i=0;i<rows.size();i++){if(i)meta<<',';meta<<rows[i].second;}meta<<"],\"inputs_hex\":[";for(size_t i=0;i<initial.size();i++){if(i)meta<<',';meta<<'"'<<hex(initial[i])<<'"';}meta<<']';
 auto emitPerms=[&](char const*name,std::vector<std::vector<int>>const&ps){meta<<",\""<<name<<"\":[";for(size_t a=0;a<ps.size();a++){if(a)meta<<',';meta<<'[';for(size_t i=0;i<ps[a].size();i++){if(i)meta<<',';meta<<ps[a][i];}meta<<']';}meta<<']';};
 emitPerms("vertex_perms",vertexPerms);emitPerms("row_perms",rowPerms);emitPerms("row_inverse_perms",rowInversePerms);meta<<",\"orientation\":\"lexicographic_minimum_sorted_multiset\",\"score_order\":\"coverage_then_orientation_then_score\"}\n";meta.close();
 std::unordered_map<State,Parent,Hash> cur,next;Parent init;init.aut=initialOriented.second;cur.emplace(initial,init);auto started=std::chrono::steady_clock::now();uint64_t candidates=0;
 auto covered=[&](State const&s){U c=0;for(U w:s)c|=(w>>k)&~w;return(c&mask)==mask;};
 auto value6=[](U w,uint64_t code){bool a=bool((w>>int(code&1023))&U(1)),b=bool((w>>int((code>>10)&1023))&U(1)),c=bool((w>>int((code>>20)&1023))&U(1)),d=bool((w>>int((code>>30)&1023))&U(1)),e=bool((w>>int((code>>40)&1023))&U(1)),f=bool((w>>int((code>>50)&1023))&U(1));int x=int(b)+int(c),y=int(!e)+int(!f);return a?(d?y:std::max(x,std::max(y,x+y-1))):(d?0:x);};
 auto blocked=[&](State const&ws,int remaining){if(ws.size()!=size_t(remaining+1))return false;for(uint64_t code:codes){int target=value6(goal,code),sum=0;for(U w:ws){sum+=value6(w,code);if(sum>=target)break;}if(sum<target)return true;}return false;};
 std::cout<<"automorphisms="<<rowPerms.size()<<" k="<<k<<" initial_auto="<<init.aut<<std::endl;
 for(int s=budget;s>=0;s--){
  double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();std::cout<<"remaining="<<s<<" states="<<cur.size()<<" candidates="<<candidates<<" cached_wires="<<transformed.size()<<" seconds="<<sec<<std::endl;
  std::ofstream out(prefix+".layer"+std::to_string(s)+".jsonl"),parents(prefix+".parents"+std::to_string(s)+".jsonl");for(auto const&entry:cur){auto const&ws=entry.first;auto const&r=entry.second;out<<'[';for(size_t j=0;j<ws.size();j++){if(j)out<<',';out<<'"'<<hex(ws[j])<<'"';}out<<"]\n";parents<<"{\"parent\":"<<r.parent<<",\"kind\":"<<r.kind<<",\"a\":"<<r.a<<",\"b\":"<<r.b<<",\"op\":"<<r.op<<",\"keep\":"<<r.keep<<",\"auto\":"<<r.aut<<"}\n";}out.close();parents.close();
  if(s==0){bool sat=cur.count(State{goal});std::cout<<(sat?"SURVIVING_GOAL":"EXHAUSTED")<<std::endl;return sat?10:0;}
  next.clear();bool over=false;
  auto add=[&](State w,Parent record){candidates++;if(w.size()>size_t(s)||!covered(w))return;auto oriented=orient(std::move(w));if(blocked(oriented.first,s-1))return;record.aut=oriented.second;next.emplace(std::move(oriented.first),record);if(next.size()>limit)over=true;};
  size_t parentIndex=0;
  for(auto const&entry:cur){auto const&ws=entry.first;int width=ws.size(),slack=s+1-width;
   if(slack>=1){Parent r;r.parent=parentIndex;r.kind=1;add(ws,r);}
   for(int i=0;i<width;i++){
    if(slack>=2){State w=ws;w.push_back(ws[i]);Parent r;r.parent=parentIndex;r.kind=2;r.a=i;add(std::move(w),r);}
    for(int j=i+1;j<width;j++)for(int op=0;op<2;op++)for(int keep=0;keep<4;keep++){
     int saves=(keep&1)+((keep>>1)&1);if(slack<saves)continue;State w;w.reserve(width+1);w.push_back(op?(ws[i]|ws[j]):(ws[i]&ws[j]));for(int l=0;l<width;l++)if(l!=i&&l!=j)w.push_back(ws[l]);if(keep&1)w.push_back(ws[i]);if(keep&2)w.push_back(ws[j]);Parent r;r.parent=parentIndex;r.kind=3;r.a=i;r.b=j;r.op=op;r.keep=keep;add(std::move(w),r);
    }
   }
   parentIndex++;
   if(over){std::cout<<"STATE_CAP remaining="<<s-1<<" partial_states="<<next.size()<<std::endl;return 11;}
   if(std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>180){std::cout<<"TIME_CAP remaining="<<s-1<<" partial_states="<<next.size()<<std::endl;return 12;}
  }
  cur.swap(next);
 }
}
