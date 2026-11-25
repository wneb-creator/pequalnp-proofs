#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <csignal>
using namespace std;
using Word=unsigned long long;
using Bits=array<Word,16>;
struct Gate {int op,a,b;};
using Circuit=array<Gate,18>;
mt19937 rng(188401);
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Bits,11> inputs;
Bits target;
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
vector<int> covers;
int notLo=1,notHi=16,readerLimit=0;
bool railReader(Gate g){return g.a==0||g.a==10||(g.op!=2&&(g.b==0||g.b==10));}
int effectiveReaders(const Circuit&c){int n=0;for(auto g:c)n+=railReader(g);return n;}
vector<int> samples={3,6,12,13,17,24,33,50,66,69,104,116,132,133,138,160,200,201,208,264,265,276,288,320,321,385,402,521,528,548,554,576,577,640,641,770,772,773,0,1,1022,1023};
int blocks=1;
Bits rowMasks{};
void rebuild(){
 for(auto& b:inputs)b.fill(0);target.fill(0);rowMasks.fill(0);blocks=(samples.size()+63)/64;
 for(size_t r=0;r<samples.size();r++){int x=samples[r];rowMasks[r/64]|=1ULL<<(r%64);for(int j=0;j<10;j++)if(x>>j&1)inputs[j][r/64]|=1ULL<<(r%64);for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[r/64]|=1ULL<<(r%64);break;}}
 for(int k=0;k<blocks;k++)inputs[10][k]=~inputs[0][k]&rowMasks[k];
 cout<<"SAMPLES [";for(size_t r=0;r<samples.size();r++){if(r)cout<<",";cout<<samples[r];}cout<<"]"<<endl;
}
bool refine(const Circuit&c){
 vector<int>errors;
 for(int x=0;x<1024;x++){
  array<bool,29>w{};for(int j=0;j<10;j++)w[j]=(x>>j)&1;w[10]=!w[0];
  for(int i=0;i<18;i++){auto g=c[i];w[11+i]=g.op==0?(w[g.a]&&w[g.b]):g.op==1?(w[g.a]||w[g.b]):!w[g.a];}
  bool want=false;for(auto[a,b]:edges)want|=(x>>a&1)&&(x>>b&1);if(w[28]!=want)errors.push_back(x);
 }
 if(errors.empty()){
  cout<<"FULL_WITNESS {\"inputs\":11,\"output\":28,\"gates\":[";for(int i=0;i<18;i++){if(i)cout<<",";auto g=c[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;return true;
 }
 shuffle(errors.begin(),errors.end(),rng);int added=0;
 for(int x:errors)if(find(samples.begin(),samples.end(),x)==samples.end()){samples.push_back(x);if(++added==16)break;}
 if(!added){cerr<<"FAULT zero sampled error disagrees with full validation"<<endl;exit(2);}
 cout<<"REFINE full_errors "<<errors.size()<<" added "<<added<<" rows "<<samples.size()<<endl;rebuild();return false;
}

int rawScore(const Circuit& c){
 array<Bits,29> w{};
 for(int j=0;j<11;j++) w[j]=inputs[j];
 bool hasnot=false;
 for(int i=0;i<18;i++){
  auto g=c[i];hasnot|=g.op==2;
  for(int k=0;k<blocks;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int s=0;
 for(int k=0;k<blocks;k++)s+=__builtin_popcountll(w[28][k]&~target[k]&rowMasks[k])*4+__builtin_popcountll(~w[28][k]&target[k]&rowMasks[k]);
 return s;
}
bool activePaid(const Circuit&c){array<bool,29>used{};used[28]=true;bool active=false;for(int i=17;i>=0;i--)if(used[11+i]){auto g=c[i];active|=g.op==2;used[g.a]=true;if(g.op!=2)used[g.b]=true;}return active;}
int railMask(const Circuit&c){array<bool,29>used{};used[28]=true;for(int i=17;i>=0;i--)if(used[11+i]){auto g=c[i];used[g.a]=true;if(g.op!=2)used[g.b]=true;}return int(used[0])+2*int(used[10]);}
bool readerPattern(Gate g){if(g.op==2)return true;bool p=g.a==0||g.b==0,n=g.a==10||g.b==10;return (!p||g.op==1)&&(!n||g.op==0);}
int searchPenalty(const Circuit&c){int rails=railMask(c);return (activePaid(c)?0:8)+((rails&1)?0:8)+((rails&2)?0:8);}
int score(const Circuit&c){return rawScore(c)+searchPenalty(c);}
void show(const Circuit& c,int s,long long trial){
 cout<<"best "<<s<<" trial "<<trial<<" gates [";
 for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";
 cout<<"]"<<endl;
}
Circuit seed(){
 int cover=covers[rng()%covers.size()];int dropA=rng()%15,dropB=rng()%14;if(dropB>=dropA)dropB++;int ei=0;
 array<vector<int>,10> star;
 for(auto [a,b]:edges){int edgei=ei++;if(edgei==dropA||edgei==dropB)continue;if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}
 vector<int> centers;for(int v=0;v<10;v++)if(!star[v].empty())centers.push_back(v);
 shuffle(centers.begin(),centers.end(),rng);
 vector<Gate> g;vector<int> roots;
 for(int v:centers){
  shuffle(star[v].begin(),star[v].end(),rng);int cur=star[v][0];
  for(size_t j=1;j<star[v].size();j++){g.push_back({1,cur,star[v][j]});cur=10+g.size();}
  g.push_back({0,v,cur});roots.push_back(10+g.size());
 }
 shuffle(roots.begin(),roots.end(),rng);
 int cur=roots[0];
 for(size_t j=1;j<roots.size();j++){g.push_back({1,cur,roots[j]});cur=10+g.size();}
 // Gate indexing is 11+i, accounting for free NOT(input0) source10.
 while(g.size()>18){
  int d=rng()%(g.size()-1);int replacement=(rng()%2)?g[d].a:g[d].b;
  int wire=11+d;
  for(size_t i=d+1;i<g.size();i++)for(int *p:{&g[i].a,&g[i].b}){
   if(*p==wire)*p=replacement;else if(*p>wire)--*p;
  }
  g.erase(g.begin()+d);
 }
 while(g.size()<18)g.push_back({0,int(10+g.size()),int(10+g.size())});
 Circuit c;copy(g.begin(),g.end(),c.begin());
 int p=notLo+rng()%(notHi-notLo+1),a=11+rng()%p;c[p]={2,a,a};int u=rng()%10,v=rng()%9;if(v>=u)v++;c[0]={1,u,v};
 for(int i=0;i<18;i++)if(c[i].op!=2&&(c[i].a==0||c[i].b==0))c[i].op=1;
 vector<int>choices;for(int i=1;i<17;i++)if(c[i].op!=2&&c[i].a!=0&&c[i].b!=0)choices.push_back(i);
 if(choices.empty())return seed();int negReader=choices[rng()%choices.size()];int partner=c[negReader].a;if(partner==10)partner=1+rng()%9;c[negReader]={0,10,partner};
 if(readerLimit&&effectiveReaders(c)>readerLimit)return seed();
 return c;
}

array<Bits,29> values(const Circuit& c){
 array<Bits,29> w{};
 for(int j=0;j<11;j++) w[j]=inputs[j];
 for(int i=0;i<18;i++){
  auto g=c[i];
  for(int k=0;k<blocks;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 return w;
}
Bits forceOutput(const Circuit& c,array<Bits,29> w,int i,Word val){
 w[11+i].fill(val);
 for(int j=i+1;j<18;j++){
  auto g=c[j];
  for(int k=0;k<blocks;k++) w[11+j][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 return w[28];
}
int coordinate(Circuit& c,int i,int temperature){
 auto w=values(c);Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL);
 Bits care,want,negative;
 for(int k=0;k<blocks;k++){care[k]=(f0[k]^f1[k])&rowMasks[k];want[k]=target[k]^f0[k];negative[k]=~target[k];}
 int readers=effectiveReaders(c)-railReader(c[i]);
 int nn=0;for(int j=0;j<18;j++)if(j!=i&&c[j].op==2)nn++;
 int best=1000000,count=0;Gate selected=c[i];
 for(int op=0;op<3;op++)for(int a=0;a<11+i;a++)for(int b=(op==2?a:0);b<=(op==2?a:a);b++){
  if((c[i].op==2)!=(op==2))continue;if(op==2&&a<11)continue;if(i==0&&(op!=1||a>=10||b>=10||a==b))continue;if(readerLimit&&readers+railReader({op,a,b})>readerLimit)continue;if(!readerPattern({op,a,b}))continue;int sc=0;
  for(int k=0;k<blocks;k++){
   Word v=op==0?(w[a][k]&w[b][k]):op==1?(w[a][k]|w[b][k]):~w[a][k];
   Word err=(v^want[k])&care[k];
   sc+=__builtin_popcountll(err)+3*__builtin_popcountll(err&negative[k]);
  }
  Gate old=c[i];c[i]={op,a,b};sc+=searchPenalty(c);c[i]=old;
  if(temperature>0)sc+=rng()%(temperature+1);
  if(sc<best){best=sc;count=1;selected={op,a,b};}
  else if(sc==best&&rng()%++count==0)selected={op,a,b};
 }
 c[i]=selected;return score(c);
}

int negationRepair(Circuit&c,int temperature){
 int j=-1;for(int k=0;k<18;k++)if(c[k].op==2)j=k;if(j<0||j==17)return score(c);
 vector<int>consumers;for(int k=j+1;k<18;k++)if(c[k].a==11+j||c[k].b==11+j)consumers.push_back(k);
 int i=consumers.empty()?17:consumers[rng()%consumers.size()];
 Gate keepJ=c[j],keepI=c[i];int readers=effectiveReaders(c)-railReader(c[i]);int best=1000000,count=0;
 for(int a=11;a<11+j;a++)for(int op=0;op<2;op++)for(int d=0;d<11+i;d++)if(d!=11+j){
  if(readerLimit&&readers+railReader({op,11+j,d})>readerLimit)continue;if(!readerPattern({op,11+j,d}))continue;
  c[j]={2,a,a};c[i]={op,11+j,d};int sc=score(c);
  if(sc==0)return 0;
  if(temperature)sc+=rng()%(temperature+1);
  if(sc<best){best=sc;count=1;keepJ=c[j];keepI=c[i];}
  else if(sc==best&&rng()%++count==0){keepJ=c[j];keepI=c[i];}
 }
 c[j]=keepJ;c[i]=keepI;return score(c);
}

int main(int argc,char**argv){signal(SIGINT,stopped);signal(SIGTERM,stopped);
 unsigned seedNo=argc>1?stoul(argv[1]):1042592;int secs=argc>2?stoi(argv[2]):900;
 rng.seed(seedNo);if(argc>3){int partition=stoi(argv[3]);if(partition==0){notLo=1;notHi=8;}else if(partition==1){notLo=9;notHi=16;}else if(partition==2){notLo=9;notHi=15;}}if(argc>4)readerLimit=stoi(argv[4]);if(argc>5){int profile=stoi(argv[5]);for(int x=0;x<1024;x++){int weight=__builtin_popcount((unsigned)x);bool take=profile==1?(x==0||x==1||x==1022||x==1023):profile==2?(weight<=2||weight>=9):false;if(take&&find(samples.begin(),samples.end(),x)==samples.end())samples.push_back(x);}}
 rebuild();
 for(int c=0;c<1024;c++)if(__builtin_popcount((unsigned)c)==6){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}
 auto start=chrono::steady_clock::now();int global=10000;Circuit best;long long trial=0;
 vector<Circuit> archive;
 for(int run=0;;run++){
  Circuit c=seed();
  if(!archive.empty()&&rng()%3){c=archive[rng()%archive.size()];for(int j=0;j<3+int(rng()%10);j++){int i=rng()%18;c[i]={c[i].op==2?2:int(rng()%2),int(rng()%(11+i)),int(rng()%(11+i))};}}
  for(int i=1;i<18;i++)if(c[i].op==2&&c[i].a<11)c[i].a=11+rng()%i;
  c[0].op=1;if(c[0].a>=10||c[0].b>=10||c[0].a==c[0].b){int u=rng()%10,v=rng()%9;if(v>=u)v++;c[0]={1,u,v};}
  for(int i=1;i<18;i++)if(c[i].op!=2){bool p=c[i].a==0||c[i].b==0,n=c[i].a==10||c[i].b==10;if(p&&n){if(c[i].a==10)c[i].a=1+rng()%9;if(c[i].b==10)c[i].b=1+rng()%9;n=false;}if(p)c[i].op=1;else if(n)c[i].op=0;}
  if(readerLimit&&effectiveReaders(c)>readerLimit)c=seed();
  int s=score(c),loc=s;Circuit local=c;
  for(int iter=0;iter<4000;iter++,trial++){
   if(trial%1000==0 && (stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs)){cout<<"done "<<trial<<" best "<<global<<endl;return 0;}
   int temp=(iter%400<250)?0:(iter%400<350?8:48);
   s=coordinate(c,rng()%18,temp);if(iter%100==0)s=negationRepair(c,temp/4);
   if(rawScore(c)==0){show(c,0,trial);if(refine(c))return 0;global=10000;archive.clear();break;}
   if(s<loc){local=c;loc=s;}
   if(s<global){best=c;global=s;show(best,rawScore(best),trial);if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}
   if(s<=global+8&&rng()%100==0){if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}
   if(iter%400==399){c=local;s=loc;}
  }
 }
}
