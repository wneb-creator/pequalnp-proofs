#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using U=uint64_t;
constexpr int N=6, LINES=11, INPUTS=17, GATES=28, WIRES=45;
constexpr int P[N]={0,1,2,3,6,7};
constexpr int Q[LINES]={0,1,2,3,6,7,8,9,10,11,12};
struct Gate { int op,a,b; };
using Net=std::array<Gate,GATES>;
std::vector<U> val,target,negative,masks;
int words=0,canonical=-1,lastRaw=0,lastFp=0,lastJoint=0,lastAccepted=0;
std::vector<int>edgeA,edgeB;
bool incident(int p,int l){int d=(P[p]+Q[l])%13;return d==0||d==1||d==3||d==9;}
int eval(Net& c){
 unsigned char good[WIRES]={};good[0]=1;good[N]=2;
 U rp[WIRES]={},rl[WIRES]={},rg[WIRES]={};for(int i=0;i<INPUTS;i++){if(i<N)rp[i]=val[i*words]&target[0];else rl[i]=val[i*words]&target[0];}
 int duplicate=0,inputDuplicate=0,emptyProfile=0;
 for(int j=0;j<GATES;j++){
  auto g=c[j];U*d=&val[(INPUTS+j)*words];const U*a=&val[g.a*words],*b=&val[g.b*words];
  if(g.op)for(int k=0;k<words;k++)d[k]=a[k]|b[k];else for(int k=0;k<words;k++)d[k]=a[k]&b[k];
  int profileCount=0,only=-1;for(int k=0;k<words;k++){U bits=d[k]&target[k];profileCount+=std::popcount(bits);if(bits)only=64*k+std::countr_zero(bits);}
  if(profileCount==1){g={0,edgeA[only],edgeB[only]};c[j]=g;for(int k=0;k<words;k++)d[k]=val[g.a*words+k]&val[g.b*words+k];}
  if(g.op){rp[INPUTS+j]=rp[g.a]|rp[g.b];rl[INPUTS+j]=rl[g.a]|rl[g.b];rg[INPUTS+j]=rg[g.a]|rg[g.b];}else rg[INPUTS+j]=(rp[g.a]&rl[g.b])|(rl[g.a]&rp[g.b]);
  int aa=good[g.a],bb=good[g.b];good[INPUTS+j]=g.op?(aa|bb):(((aa&1)&&(bb&2))||((aa&2)&&(bb&1))?4:0);
  duplicate+=g.a==g.b;emptyProfile+=profileCount==0;
  for(int i=0;i<INPUTS;i++)if(d[0]==val[i*words]){bool equal=true;for(int k=1;k<words;k++)if(d[k]!=val[i*words+k]){equal=false;break;}if(equal){inputDuplicate++;break;}}
 }
 lastRaw=0;lastFp=0;
 U*out=&val[(WIRES-1)*words];
 for(int k=0;k<words;k++){U err=(target[k]^out[k])&masks[k];lastRaw+=std::popcount(err);lastFp+=std::popcount(err&negative[k]);}
 lastJoint=(out[0]&target[0]&~rg[WIRES-1])==0;
 lastAccepted=(out[canonical/64]>>(canonical%64))&1;
 return 8*(lastRaw-lastFp)+lastFp+16*lastJoint+4*duplicate+4*inputDuplicate+4*emptyProfile;
}
void show(const Net& c,int score,long long it,double seconds){
 std::cout<<"{\"seconds\":"<<seconds<<",\"score\":"<<score<<",\"raw\":"<<lastRaw<<",\"fp\":"<<lastFp<<",\"joint\":"<<lastJoint<<",\"accepted\":"<<lastAccepted<<",\"iterations\":"<<it<<",\"gates\":[";
 for(int j=0;j<GATES;j++){auto g=c[j];if(j)std::cout<<",";std::cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}
 std::cout<<"]}"<<std::endl;
}
std::vector<Gate> star(std::mt19937& rng){
 std::vector<Gate> c;std::vector<int> roots;std::array<int,N> order;
 std::iota(order.begin(),order.end(),0);std::shuffle(order.begin(),order.end(),rng);bool sides=false;
 int duplicatePoint=0;
 if(rng()%2){if(rng()%2){c.push_back({0,0,0});duplicatePoint=INPUTS;}else{int other=1+rng()%(INPUTS-1);c.push_back({1,0,other});c.push_back({0,0,INPUTS});duplicatePoint=INPUTS+1;}}
 auto inp=[&](int i){return i==0?duplicatePoint:i;};
 for(int i:order){std::vector<int> nb;for(int j=0;j<LINES;j++)if(sides?incident(j,i):incident(i,j))nb.push_back(inp(sides?j:N+j));
  std::shuffle(nb.begin(),nb.end(),rng);int a=nb[0];for(int k=1;k<4;k++){int d=INPUTS+c.size();c.push_back({1,a,nb[k]});a=d;}
  int d=INPUTS+c.size();c.push_back({0,inp(sides?N+i:i),a});roots.push_back(d);
 }
 while(roots.size()>1){int ia=rng()%roots.size(),a=roots[ia];roots.erase(roots.begin()+ia);int ib=rng()%roots.size(),b=roots[ib];roots.erase(roots.begin()+ib);int d=INPUTS+c.size();c.push_back({1,a,b});roots.push_back(d);}
 return c;
}
Net deleteGate(std::vector<Gate> base,std::mt19937& rng){
 int protect=0;
 if(base[0].op==0&&base[0].a==0&&base[0].b==0)protect=1;
 if(base[0].op==1&&base[0].a==0&&base[1].op==0&&base[1].a==0&&base[1].b==INPUTS)protect=2;
 while(base.size()>GATES){
  std::vector<int>eligible;for(int j=protect;j<(int)base.size()-1;j++)if(base[j].op==1&&(base[j].a<INPUTS||base[j].b<INPUTS))eligible.push_back(j);
  int rem=(!eligible.empty()&&rng()%4)?eligible[rng()%eligible.size()]:protect+rng()%(base.size()-1-protect);
  int sub=base[rem].a>=INPUTS?base[rem].a:base[rem].b>=INPUTS?base[rem].b:rng()%2?base[rem].a:base[rem].b;
  base.erase(base.begin()+rem);for(auto&q:base){auto fix=[&](int v){if(v==INPUTS+rem)v=sub;if(v>INPUTS+rem)v--;return v;};q.a=fix(q.a);q.b=fix(q.b);}}
 Net c;std::copy(base.begin(),base.end(),c.begin());return c;
}
void mutate(Net&c,std::mt19937&rng,int strength){
 for(int t=0;t<strength;t++){
  int j=rng()%GATES,kind=rng()%20;auto&g=c[j];
  if(kind<2)g.op=1-g.op;
  else if(kind<8)g.a=rng()%(INPUTS+j);
  else if(kind<14)g.b=rng()%(INPUTS+j);
  else if(kind==14)g={int(rng()%2),int(rng()%(INPUTS+j)),int(rng()%(INPUTS+j))};
  else if(kind==15){int old=rng()%(INPUTS+j),sub=rng()%(INPUTS+j);for(int k=j;k<GATES;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==16){int old=INPUTS+j,sub=rng()%2?g.a:g.b;for(int k=j+1;k<GATES;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==17){int h=rng()%GATES;std::swap(c[h].op,c[j].op);}
  else if(kind==18){
   int a=g.a,b=g.b;if(a<INPUTS)std::swap(a,b);if(a>=INPUTS){int h=a-INPUTS;int uses=0;for(int k=h+1;k<GATES;k++)uses+=(c[k].a==a)+(c[k].b==a);
    if(uses==1&&c[h].op==g.op&&b<INPUTS+h){int displaced=c[h].b;c[h].b=b;g.a=a;g.b=displaced;}}
  }else{int h=rng()%GATES;if(h<j)std::swap(h,j);if(h!=j&&c[h].a<INPUTS+j&&c[h].b<INPUTS+j){std::swap(c[h],c[j]);for(int k=j+1;k<GATES;k++){if(c[k].a==INPUTS+j)c[k].a=INPUTS+h;else if(c[k].a==INPUTS+h)c[k].a=INPUTS+j;if(c[k].b==INPUTS+j)c[k].b=INPUTS+h;else if(c[k].b==INPUTS+h)c[k].b=INPUTS+j;}}}
 }
}
bool valid(const Net&c){for(int j=0;j<GATES;j++)if(c[j].a>=INPUTS+j||c[j].b>=INPUTS+j)return false;return true;}
int main(int argc,char**argv){
 if(argc!=4)return 2;std::ifstream f(argv[1]);int row;std::vector<int>rows;while(f>>row)rows.push_back(row);if(rows.size()!=76)return 3;
 words=(rows.size()+63)/64;edgeA.resize(rows.size());edgeB.resize(rows.size());val.resize(WIRES*words);target.resize(words);negative.resize(words);masks.resize(words);
 for(int k=0;k<(int)rows.size();k++){
  int r=rows[k],b=k%64,w=k/64;if(r==(1|(1<<N)))canonical=k;
  for(int i=0;i<INPUTS;i++)if((r>>i)&1)val[i*words+w]|=U(1)<<b;
  bool y=false;for(int p=0;p<N;p++)for(int l=0;l<LINES;l++)if(incident(p,l)&&((r>>p)&1)&&((r>>(N+l))&1))y=true;
  if(y){target[w]|=U(1)<<b;edgeA[k]=std::countr_zero((unsigned)r);edgeB[k]=std::countr_zero((unsigned)(r&(r-1)));}else negative[w]|=U(1)<<b;masks[w]|=U(1)<<b;
 }
 if(canonical<0)return 4;
 std::mt19937 rng(std::stoul(argv[3]));int seconds=std::stoi(argv[2]);
 for(int trial=0;trial<64;trial++){
  auto base=star(rng);std::vector<U>cv((INPUTS+base.size())*words);std::copy(val.begin(),val.begin()+INPUTS*words,cv.begin());
  for(int j=0;j<(int)base.size();j++){auto g=base[j];for(int k=0;k<words;k++)cv[(INPUTS+j)*words+k]=g.op?(cv[g.a*words+k]|cv[g.b*words+k]):(cv[g.a*words+k]&cv[g.b*words+k]);}
  for(int k=0;k<words;k++)if(((cv[(INPUTS+base.size()-1)*words+k]^target[k])&masks[k])!=0){std::cerr<<"seed control failed"<<std::endl;return 5;}
 }
 std::cerr<<"PASS64 randomized positive seed controls"<<std::endl;
 auto start=std::chrono::steady_clock::now();auto elapsed=[&]{return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 Net best{};int bs=100000,bestRaw=100000;std::vector<Net>pool;long long it=0;int restarts=0;
 while(elapsed()<seconds){
  Net c;if(!pool.empty()&&rng()%3){c=pool[rng()%pool.size()];mutate(c,rng,1+rng()%5);if(!valid(c))c=deleteGate(star(rng),rng);}else c=deleteGate(star(rng),rng);
  int sc=eval(c),cycle=30000+int(rng()%70000);double initial=4.0+double(rng()%6000)/100.0;
  for(int z=0;z<cycle;z++,it++){
   Net nc=c;int strength=1;auto rm=rng()%100;if(rm<10)strength=2;else if(rm<13)strength=3+rng()%4;mutate(nc,rng,strength);if(!valid(nc))continue;
   int ns=eval(nc),rr=lastRaw;
   if(ns<bs||(ns==bs&&rr<bestRaw)){bs=ns;bestRaw=rr;best=nc;show(best,ns,it,elapsed());}
   if(rr==0){show(nc,ns,it,elapsed());return 0;}
   if(ns<=bs+24&&rng()%200==0){if(pool.size()<128)pool.push_back(nc);else pool[rng()%pool.size()]=nc;}
   double temp=0.1+initial*std::exp(-double(z)/(cycle/6.0));
   bool accept=ns<=sc||std::generate_canonical<double,32>(rng)<std::exp(double(sc-ns)/temp);if(accept){c=nc;sc=ns;}
  }
  restarts++;if(restarts%20==0){int sc=eval(best);show(best,sc,it,elapsed());}
 }
 int sc=eval(best);show(best,sc,it,elapsed());return 0;
}
