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
using Bits=array<Word,1>;
struct Gate {int op,a,b;};
using Circuit=array<Gate,18>;
mt19937 rng(188401);
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Bits,11> inputs;
Bits target;
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
vector<int> covers;
bool activeFree(const Circuit&c){
 array<Word,29>lo{},hi{};for(int i=0;i<10;i++)lo[i]=hi[i]=inputs[i][0];hi[10]=(1ULL<<38)-1;
 for(int i=0;i<18;i++){auto g=c[i];lo[11+i]=g.op?(lo[g.a]|lo[g.b]):(lo[g.a]&lo[g.b]);hi[11+i]=g.op?(hi[g.a]|hi[g.b]):(hi[g.a]&hi[g.b]);}
 Word delta=lo[28]^hi[28];return (delta&inputs[10][0])&&(delta&~inputs[10][0]);
}
int score(const Circuit& c){
 array<Bits,29> w;
 for(int j=0;j<11;j++) w[j]=inputs[j];
 bool hasnot=false;
 for(int i=0;i<18;i++){
  auto g=c[i];hasnot|=g.op==2;
  for(int k=0;k<1;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int s=0;
 for(int k=0;k<1;k++)s+=__builtin_popcountll(w[28][k]&~target[k])*4+__builtin_popcountll(~w[28][k]&target[k]);
 return 16*s+!activeFree(c);
}
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
 
 return c;
}

array<Bits,29> values(const Circuit& c){
 array<Bits,29> w;
 for(int j=0;j<11;j++) w[j]=inputs[j];
 for(int i=0;i<18;i++){
  auto g=c[i];
  for(int k=0;k<1;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 return w;
}
Bits forceOutput(const Circuit& c,array<Bits,29> w,int i,Word val){
 w[11+i].fill(val);
 for(int j=i+1;j<18;j++){
  auto g=c[j];
  for(int k=0;k<1;k++) w[11+j][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 return w[28];
}
int coordinate(Circuit& c,int i,int temperature){
 auto w=values(c);Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL);
 Bits care,want,negative;
 for(int k=0;k<1;k++){care[k]=f0[k]^f1[k];want[k]=target[k]^f0[k];negative[k]=~target[k];}
 int nn=0;for(int j=0;j<18;j++)if(j!=i&&c[j].op==2)nn++;
 int best=1000000,count=0;Gate selected=c[i];
 for(int op=0;op<2;op++)for(int a=0;a<11+i;a++)for(int b=(op==2?a:0);b<=(op==2?a:a);b++){
  if(op==2&&nn>0)continue;int sc=0;
  for(int k=0;k<1;k++){
   Word v=op==0?(w[a][k]&w[b][k]):op==1?(w[a][k]|w[b][k]):~w[a][k];
   Word err=(v^want[k])&care[k];
   sc+=__builtin_popcountll(err)+3*__builtin_popcountll(err&negative[k]);
  }
  Gate old=c[i];c[i]={op,a,b};sc=16*sc+!activeFree(c);c[i]=old;
  if(temperature>0)sc+=rng()%(temperature+1);
  if(sc<best){best=sc;count=1;selected={op,a,b};}
  else if(sc==best&&rng()%++count==0)selected={op,a,b};
 }
 c[i]=selected;return score(c);
}

int resubstitute(Circuit&c,int temperature){
 array<bool,29>live{};live[28]=true;
 for(int i=17;i>=0;i--)if(live[11+i]){live[c[i].a]=true;live[c[i].b]=true;}
 vector<pair<int,int>>pairs;
 for(int j=0;j<17;j++)for(int i=j+1;i<18;i++)if(live[11+i]){
  bool valid=true;for(int k=j+1;k<18;k++)if(k!=i&&(c[k].a==11+j||c[k].b==11+j))valid=false;
  if(valid)pairs.push_back({j,i});
 }
 if(pairs.empty())return score(c);
 auto[j,i]=pairs[rng()%pairs.size()];auto w=values(c);
 Word f0=forceOutput(c,w,i,0)[0],f1=forceOutput(c,w,i,~0ULL)[0],care=f0^f1,want=target[0]^f0;
 Gate keepJ=c[j],keepI=c[i];int best=100000,count=0;
 for(int op=0;op<2;op++)for(int a=0;a<11+j;a++)for(int b=0;b<=a;b++){
  Word h=op?(w[a][0]|w[b][0]):(w[a][0]&w[b][0]);
  for(int op2=0;op2<2;op2++)for(int d=0;d<11+i;d++)if(d!=11+j){
   Word value=op2?(h|w[d][0]):(h&w[d][0]),bad=(value^want)&care;
   int sc=__builtin_popcountll(bad)+3*__builtin_popcountll(bad&~target[0]);
   Gate oldJ=c[j],oldI=c[i];c[j]={op,a,b};c[i]={op2,11+j,d};sc=16*sc+!activeFree(c);c[j]=oldJ;c[i]=oldI;
   if(temperature)sc+=rng()%(temperature+1);
   if(sc<best){best=sc;count=1;keepJ={op,a,b};keepI={op2,11+j,d};}
   else if(sc==best&&rng()%++count==0){keepJ={op,a,b};keepI={op2,11+j,d};}
  }
 }
 c[j]=keepJ;c[i]=keepI;return score(c);
}

int main(int argc,char**argv){signal(SIGINT,stopped);signal(SIGTERM,stopped);
 unsigned seedNo=argc>1?stoul(argv[1]):1042592;int secs=argc>2?stoi(argv[2]):900;
 rng.seed(seedNo);
 vector<int>rows={3,6,12,13,17,24,33,50,66,69,104,116,132,133,138,160,200,201,208,264,265,276,288,320,321,385,402,521,528,548,554,576,577,640,641,770,772,773};
 for(size_t r=0;r<rows.size();r++){int x=rows[r];
  for(int j=0;j<10;j++)if(x>>j&1)inputs[j][0]|=1ULL<<r;
  for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[0]|=1ULL<<r;break;}
 }
 for(int k=0;k<1;k++)inputs[10][k]=~inputs[0][k]&((1ULL<<38)-1);
 for(int c=0;c<1024;c++)if(__builtin_popcount((unsigned)c)==6){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}
 auto start=chrono::steady_clock::now();int global=10000;Circuit best;long long trial=0;
 vector<Circuit> archive;
 for(int run=0;;run++){
  Circuit c=seed();
  if(!archive.empty()&&rng()%3){c=archive[rng()%archive.size()];for(int j=0;j<3+int(rng()%10);j++){int i=rng()%18;c[i]={int(rng()%2),int(rng()%(11+i)),int(rng()%(11+i))};}}
  int s=score(c),loc=s;Circuit local=c;
  for(int iter=0;iter<4000;iter++,trial++){
   if(trial%1000==0 && (stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs)){cout<<"done "<<trial<<" best "<<global<<endl;return 0;}
   int temp=(iter%400<250)?0:(iter%400<350?64:256);
   s=coordinate(c,rng()%18,temp);if(iter%100==0)s=resubstitute(c,temp?2:0);
   if(s<loc){local=c;loc=s;}
   if(s<global){best=c;global=s;show(best,global/16,trial);if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;if(global<2)return 0;}
   if(s<=global+8&&rng()%100==0){if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}
   if(iter%400==399){c=local;s=loc;}
  }
 }
}
