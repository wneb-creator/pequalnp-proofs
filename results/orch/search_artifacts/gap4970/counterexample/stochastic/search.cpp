#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <random>
#include <set>
#include <string>
#include <vector>
using U=uint64_t;
constexpr int MG=64,MW=4,NW=80;
struct Gate{int op,a,b;};
struct Star{U cover=0;int row=0;};
struct Stats{int fn=0,fp=0,miss=0,mix=0;int errors()const{return fn+fp;}int total()const{return fn+fp+miss+mix;}};
struct Circ{std::array<Gate,MG>gs{};U w[NW][MW]{};unsigned sup[NW]{},reach[NW]{};U cover[MG]{};unsigned char mixed[MG]{};int out=0;Stats st;};
int n,p,m,bound,ng,nwords;unsigned full,points,lines;
std::vector<std::pair<int,int>>edges;std::vector<int>adj[20],rows;std::vector<Star>stars;
U inputs[20][MW]{},pos[MW]{},neg[MW]{},allEdges;
std::mt19937_64 rng(4970);int rnd(int x){assert(x>0);return rng()%x;}
bool function(unsigned r){for(auto[a,b]:edges)if((r>>a&1)&&(r>>b&1))return true;return false;}
void setup(const char*path){
 std::ifstream f(path);if(!(f>>n>>p>>m>>bound))std::exit(2);ng=bound-1;assert(n<=16&&ng<MG&&n+ng<NW&&m<64);full=(1u<<n)-1;points=(1u<<p)-1;lines=full^points;allEdges=(U(1)<<m)-1;
 for(int k=0;k<m;k++){int a,b;f>>a>>b;assert(a<p&&b>=p&&b<n);edges.push_back({a,b});adj[a].push_back(b);adj[b].push_back(a);}
 std::set<int>rs;for(auto[a,b]:edges)rs.insert((1<<a)|(1<<b));int mis=0;
 for(unsigned r=0;r<=full;r++)if(!function(r)){bool maximal=true;for(int i=0;i<n;i++)if(!(r>>i&1)&&!function(r|(1u<<i)))maximal=false;if(maximal){rs.insert(r);mis++;}}
 stars.resize(1u<<n);
 for(int center=0;center<n;center++){unsigned mask=0;for(int i:adj[center])mask|=1u<<i;for(unsigned q=mask;q;q=(q-1)&mask)if(std::popcount(q)>=2){U cov=0;for(int k=0;k<m;k++){auto[a,b]=edges[k];if((a==center&&(q>>b&1))||(b==center&&(q>>a&1)))cov|=U(1)<<k;}assert(!stars[q].cover||stars[q].cover==cov);stars[q].cover=cov;rs.insert(full^q);}}
 rows.assign(rs.begin(),rs.end());assert(rows.size()<=64*MW);nwords=(rows.size()+63)/64;
 for(unsigned q=1;q<=full;q++)if(stars[q].cover)stars[q].row=std::lower_bound(rows.begin(),rows.end(),int(full^q))-rows.begin();
 for(int k=0;k<(int)rows.size();k++){unsigned r=rows[k];U bit=U(1)<<(k%64);for(int i=0;i<n;i++)if(r>>i&1)inputs[i][k/64]|=bit;
  if(std::popcount(r)==2&&function(r))pos[k/64]|=bit;
  if(!function(r)){bool maximal=true;for(int i=0;i<n;i++)if(!(r>>i&1)&&!function(r|(1u<<i)))maximal=false;if(maximal)neg[k/64]|=bit;}}
 std::printf("GRAPH n=%d edges=%d bound=%d target=%d rows=%zu maximal_independent=%d\n",n,m,bound,ng,rows.size(),mis);std::fflush(stdout);
}
void eval(Circ&c,int start=0){
 for(int j=start;j<ng;j++){auto g=c.gs[j];int v=n+j;for(int k=0;k<nwords;k++)c.w[v][k]=g.op?(c.w[g.a][k]|c.w[g.b][k]):(c.w[g.a][k]&c.w[g.b][k]);c.sup[v]=g.op?(c.sup[g.a]|c.sup[g.b]):(c.sup[g.a]&c.sup[g.b]);c.reach[v]=g.op?(c.reach[g.a]|c.reach[g.b]):0;c.mixed[j]=g.op&&(c.reach[v]&points)&&(c.reach[v]&lines);auto s=stars[c.sup[v]];c.cover[j]=(g.op&&s.cover&&!(c.w[v][s.row/64]>>(s.row%64)&1))?s.cover:0;}
 c.st={};for(int k=0;k<nwords;k++){c.st.fn+=std::popcount(pos[k]&~c.w[c.out][k]);c.st.fp+=std::popcount(neg[k]&c.w[c.out][k]);}U coverage=0;for(int j=0;j<ng;j++){coverage|=c.cover[j];c.st.mix+=c.mixed[j];}c.st.miss=std::popcount(allEdges^coverage);
}
std::pair<std::vector<Gate>,int> control(int distributed){
 std::vector<Gate>gs;std::vector<int>order,terms;int coeff[20];for(int i=0;i<p;i++)order.push_back(i);std::shuffle(order.begin(),order.end(),rng);
 for(int v:order){auto ns=adj[v];assert(ns.size()>=2);std::shuffle(ns.begin(),ns.end(),rng);int a=ns[0];for(unsigned i=1;i<ns.size();i++){gs.push_back({1,a,ns[i]});a=n+gs.size()-1;}coeff[v]=a;}
 for(int i=distributed;i<p;i++){int v=order[i];gs.push_back({0,v,coeff[v]});terms.push_back(n+gs.size()-1);}
 while(terms.size()>1){int j=rnd(terms.size()),a=terms[j];terms.erase(terms.begin()+j);j=rnd(terms.size());int b=terms[j];terms.erase(terms.begin()+j);gs.push_back({1,a,b});terms.push_back(n+gs.size()-1);}
 int out=terms[0];for(int i=0;i<distributed;i++){int v=order[i];gs.push_back({1,v,out});int a=n+gs.size()-1;gs.push_back({1,coeff[v],out});int b=n+gs.size()-1;gs.push_back({0,a,b});out=n+gs.size()-1;}
 assert((int)gs.size()==bound+distributed);return {gs,out};
}
bool verify(const std::vector<Gate>&gs,int out,bool requireHyp,const char*label){
 unsigned sup[NW]{},reach[NW]{};std::vector<bool>pure(gs.size());int mixed=0,errors=0;
 for(int i=0;i<n;i++)sup[i]=reach[i]=1u<<i;
 for(unsigned j=0;j<gs.size();j++){auto g=gs[j];assert(g.op==0||g.op==1);assert(g.a>=0&&g.a<n+(int)j&&g.b>=0&&g.b<n+(int)j);sup[n+j]=g.op?(sup[g.a]|sup[g.b]):(sup[g.a]&sup[g.b]);reach[n+j]=g.op?(reach[g.a]|reach[g.b]):0;mixed+=g.op&&(reach[n+j]&points)&&(reach[n+j]&lines);pure[j]=g.op&&stars[sup[n+j]].cover;}
 for(unsigned row=0;row<=full;row++){bool w[NW];for(int i=0;i<n;i++)w[i]=row>>i&1;for(unsigned j=0;j<gs.size();j++){auto g=gs[j];w[n+j]=g.op?(w[g.a]||w[g.b]):(w[g.a]&&w[g.b]);if(pure[j]&&w[n+j]!=bool(row&sup[n+j]))pure[j]=false;}if(w[out]!=function(row))errors++;}
 U cov=0;for(unsigned j=0;j<gs.size();j++)if(pure[j])cov|=stars[sup[n+j]].cover;
 std::printf("VALIDATE %s gates=%zu full_rows=%u wrong=%d mixed=%d missing_star_edges=%d\n",label,gs.size(),full+1,errors,mixed,std::popcount(allEdges^cov));std::fflush(stdout);
 return !errors&&(!requireHyp||(!mixed&&cov==allEdges));
}
void reorder(std::vector<Gate>&gs,int&out){
 int count=gs.size(),mapping[NW];for(int i=0;i<NW;i++)mapping[i]=-1;for(int i=0;i<n;i++)mapping[i]=i;std::vector<Gate>fresh;std::vector<int>todo;for(int i=0;i<count;i++)todo.push_back(i);
 while(!todo.empty()){std::vector<int>ready;for(unsigned i=0;i<todo.size();i++){auto g=gs[todo[i]];if(mapping[g.a]>=0&&mapping[g.b]>=0)ready.push_back(i);}int z=ready[rnd(ready.size())],j=todo[z];auto g=gs[j];mapping[n+j]=n+fresh.size();fresh.push_back({g.op,mapping[g.a],mapping[g.b]});todo.erase(todo.begin()+z);}
 out=mapping[out];gs=std::move(fresh);
}
Circ seed(){
 int z=rnd(100),d=z<50?0:z<80?1:z<95?2:3;d=std::min(d,p-1);auto[gs,out]=control(d);
 while((int)gs.size()>ng){int j=rnd(gs.size()),wire=n+j,sub=rnd(2)?gs[j].a:gs[j].b;gs.erase(gs.begin()+j);auto ren=[&](int x){if(x==wire)x=sub;return x>wire?x-1:x;};for(auto&g:gs){g.a=ren(g.a);g.b=ren(g.b);}out=ren(out);}
 reorder(gs,out);Circ c;for(int i=0;i<n;i++){c.sup[i]=c.reach[i]=1u<<i;for(int k=0;k<nwords;k++)c.w[i][k]=inputs[i][k];}for(int j=0;j<ng;j++)c.gs[j]=gs[j];c.out=out;eval(c);return c;
}
double score(const Stats&s,int island){
 if(island==0)return 4*(s.fn+s.fp)+2*s.miss+3*s.mix;
 if(island==1)return 8*s.fn+s.fp+s.miss+2*s.mix;
 if(island==2)return s.fn+s.fp+8*s.miss+4*s.mix;
 return 2*(s.fn+s.fp)+2*s.miss+16*s.mix;
}
void print(const Circ&c,unsigned long long it,double seconds,const char*label){std::printf("%s fn=%d fp=%d missing=%d mixed=%d iterations=%llu seconds=%.2f output=%d\n",label,c.st.fn,c.st.fp,c.st.miss,c.st.mix,it,seconds,c.out);for(int j=0;j<ng;j++){auto g=c.gs[j];std::printf("%d %c %d %d\n",n+j,"&|"[g.op],g.a,g.b);}std::fflush(stdout);}
void save(const Circ&c,const std::string&path){std::ofstream f(path);f<<"{\n  \"gates\": [\n";for(int j=0;j<ng;j++){auto g=c.gs[j];f<<"    ["<<g.op<<", "<<g.a<<", "<<g.b<<"]"<<(j+1==ng?"\n":",\n");}f<<"  ],\n  \"output\": "<<c.out<<",\n  \"boundary_false_negatives\": "<<c.st.fn<<",\n  \"boundary_false_positives\": "<<c.st.fp<<",\n  \"missing_star_edges\": "<<c.st.miss<<",\n  \"tCount\": "<<c.st.mix<<"\n}\n";}
void saveControl(const std::vector<Gate>&gs,int out,const std::string&path){std::ofstream f(path);f<<"{\n  \"gates\": [\n";for(unsigned j=0;j<gs.size();j++){auto g=gs[j];f<<"    ["<<g.op<<", "<<g.a<<", "<<g.b<<"]"<<(j+1==gs.size()?"\n":",\n");}f<<"  ],\n  \"output\": "<<out<<"\n}\n";}
int main(int argc,char**argv){
 if(argc<4){std::fprintf(stderr,"usage: search GRAPH.dat SECONDS OUTPUT_PREFIX [SEED]\n");return 2;}if(argc>4)rng.seed(std::strtoull(argv[4],nullptr,10));setup(argv[1]);int duration=std::atoi(argv[2]);std::string prefix=argv[3];
 for(int d=0;d<=std::min(2,p-1);d++){auto[gs,out]=control(d);if(!verify(gs,out,true,"positive-control"))return 2;saveControl(gs,out,prefix+".control"+std::to_string(d)+".json");}
 if(duration==0)return 0;
 std::vector<Circ>pop;for(int i=0;i<128;i++)pop.push_back(seed());Circ best=pop[0],bestHyp=best;int bestH=100000;bool sawTruth=false;double sec=0,nextstatus=60;unsigned long long it=0;auto start=std::chrono::steady_clock::now();print(best,0,0,"BEST");
 for(;;it++){
  if(it%131072==0){sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(sec>=duration)break;if(sec>=nextstatus){std::printf("STATUS seconds=%.2f iterations=%llu best_total=%d best_hypothesis_errors=%d\n",sec,it,best.st.total(),bestH);std::fflush(stdout);nextstatus+=60;}}
  int slot=rnd(128),island=slot%4;Circ c=pop[slot];int lo=ng;
  if(rnd(1000)==0){std::vector<Gate>gs(c.gs.begin(),c.gs.begin()+ng);int out=c.out;reorder(gs,out);std::copy(gs.begin(),gs.end(),c.gs.begin());c.out=out;lo=0;}
  else {int changes=1+(rnd(100)<30)+(rnd(100)<5?rnd(5):0);for(int z=0;z<changes;z++){int j=rnd(ng),mode=rnd(10);lo=std::min(lo,j);if(mode==0)c.gs[j].op^=1;else if(mode<5)c.gs[j].a=rnd(n+j);else if(mode<9)c.gs[j].b=rnd(n+j);else c.gs[j]=pop[rnd(128)].gs[j];}if(rnd(100)<1)c.out=n+rnd(ng);}
  eval(c,lo);double before=score(pop[slot].st,island),after=score(c.st,island),temp=(slot/4)%8==0?3.0:(slot/4)%8==1?1.0:(slot/4)%8==2?0.3:0;
  if(after<=before||(temp>0&&double(rng())/double(UINT64_MAX)<std::exp((before-after)/temp)))pop[slot]=c;
  if(c.st.total()<best.st.total()){best=c;print(c,it,sec,"BEST");save(c,prefix+".best.json");}
  if(!c.st.miss&&!c.st.mix&&c.st.errors()<bestH){bestH=c.st.errors();bestHyp=c;print(c,it,sec,"BEST_WITH_HYPOTHESES");save(c,prefix+".best-hyp.json");}
  if(!c.st.errors()&&!sawTruth){sawTruth=true;print(c,it,sec,"TRUTH_CANDIDATE");std::vector<Gate>gs(c.gs.begin(),c.gs.begin()+ng);if(!verify(gs,c.out,false,"truth-candidate"))return 3;save(c,prefix+".truth.json");}
  if(!c.st.total()){std::vector<Gate>gs(c.gs.begin(),c.gs.begin()+ng);if(!verify(gs,c.out,true,"full-counterexample"))return 3;save(c,prefix+".counterexample.json");std::puts("VERIFIED_FULL_COUNTEREXAMPLE");return 10;}
  if(it%131072==0)pop[rnd(128)]=seed();if(it%1048576==0)pop[rnd(128)]=best;if(it%2097152==0&&bestH<100000)pop[rnd(128)]=bestHyp;
 }
 print(best,it,sec,"FINAL_BEST");if(bestH<100000)print(bestHyp,it,sec,"FINAL_BEST_WITH_HYPOTHESES");std::printf("DONE no_counterexample iterations=%llu seconds=%.2f\n",it,sec);return 0;
}
