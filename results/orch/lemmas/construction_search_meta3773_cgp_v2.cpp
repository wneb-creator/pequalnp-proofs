#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
struct Gate { int op,a,b; }; // op0 AND, op1 OR
struct Score { int fn,fp,active; };
static constexpr int MAXG=140, MAXW=16;
static uint64_t words[26+MAXG][MAXW];
static int nw,nrows,ng;
static mt19937_64 rng;
static vector<Gate> gates;
static int rnd(int n) { return int(rng()%n); }
static uint64_t iterations=0;
static int bestCorrect=100000,bestWrong=100000;
static string checkpoint;
static bool active[MAXG];
static int aliasWire[26+MAXG];

static Score eval(int from=0) {
  for(int i=from;i<ng;i++) for(int w=0;w<nw;w++)
    words[26+i][w]=gates[i].op ? words[gates[i].a][w]|words[gates[i].b][w] :
      words[gates[i].a][w]&words[gates[i].b][w];
  const uint64_t pos=(uint64_t(1)<<52)-1;
  int fn=__builtin_popcountll(~words[26+ng-1][0]&pos);
  int fp=__builtin_popcountll(words[26+ng-1][0]&~pos);
  for(int w=1;w<nw;w++) fp+=__builtin_popcountll(words[26+ng-1][w]);
  array<int,512> buckets;buckets.fill(-1);
  for(int i=0;i<26+ng;i++) {
    uint64_t hash=1469598103934665603ULL;
    for(int w=0;w<nw;w++){hash^=words[i][w];hash*=1099511628211ULL;}
    int slot=hash&511;
    while(buckets[slot]>=0&&memcmp(words[i],words[buckets[slot]],nw*sizeof(uint64_t))!=0)slot=(slot+1)&511;
    if(buckets[slot]<0){buckets[slot]=i;aliasWire[i]=i;}else aliasWire[i]=buckets[slot];
  }
  fill(active,active+ng,false);
  array<int,2*MAXG+4> stack;int n=0;
  if(aliasWire[26+ng-1]>=26)stack[n++]=aliasWire[26+ng-1]-26;
  while(n) {
    int i=stack[--n];if(active[i])continue;active[i]=true;
    if(aliasWire[gates[i].a]>=26)stack[n++]=aliasWire[gates[i].a]-26;
    if(aliasWire[gates[i].b]>=26)stack[n++]=aliasWire[gates[i].b]-26;
  }
  active[0]=true; // Retain the permitted first gate even when unused.
  int count=0;for(int i=0;i<ng;i++)count+=active[i];
  return {fn,fp,count};
}
static void save(const Score&s,uint64_t seed) {
  vector<int> remap(26+ng,-1);iota(remap.begin(),remap.begin()+26,0);
  vector<Gate> out;
  for(int i=0;i<ng;i++)if(active[i]) {
    assert(remap[aliasWire[gates[i].a]]>=0&&remap[aliasWire[gates[i].b]]>=0);
    remap[26+i]=26+out.size();out.push_back({gates[i].op,remap[aliasWire[gates[i].a]],remap[aliasWire[gates[i].b]]});
  }
  ofstream f(checkpoint);
  f<<"{\"seed\":"<<seed<<",\"iterations\":"<<iterations<<",\"fn\":"<<s.fn
   <<",\"fp\":"<<s.fp<<",\"active\":"<<s.active<<",\"input_count\":26,\"output\":"
   <<remap[aliasWire[26+ng-1]]<<",\"gates\":[";
  for(size_t i=0;i<out.size();i++) {
    if(i)f<<',';f<<'['<<out[i].op<<','<<out[i].a<<','<<out[i].b<<']';
  }
  f<<"]}\n";
}
static vector<Gate> baseline() {
  vector<Gate> g;vector<int> starout;
  vector<int> lines(13);iota(lines.begin(),lines.end(),0);shuffle(lines.begin()+1,lines.end(),rng);
  auto add=[&](int op,int a,int b){int out=26+g.size();g.push_back({op,a,b});return out;};
  for(int l:lines) {
    vector<int> p;
    for(int x=0;x<13;x++){int s=(x+l)%13;if(s==0||s==1||s==3||s==9)p.push_back(x);}
    if(l)shuffle(p.begin(),p.end(),rng);
    assert(l|| (p[0]==0&&p[1]==1));
    int a=add(1,p[0],p[1]),u;
    if(rnd(2)){int b=add(1,p[2],p[3]);u=add(1,a,b);}
    else {int b=add(1,a,p[2]);u=add(1,b,p[3]);}
    starout.push_back(add(0,13+l,u));
  }
  while(starout.size()>1) {
    int a=rnd(starout.size());int x=starout[a];starout.erase(starout.begin()+a);
    int b=rnd(starout.size());int y=starout[b];starout.erase(starout.begin()+b);
    starout.push_back(add(1,x,y));
  }
  assert(g.size()==64);return g;
}
static vector<Gate> nonstar_baseline() {
  vector<Gate> g;vector<int> out;auto add=[&](int op,int a,int b){int w=26+g.size();g.push_back({op,a,b});return w;};
  int z=rnd(2)?3:9;vector<int> group{0};
  for(int l=1;l<13;l++){int s=(l+z)%13;if(s==0||s==1||s==3||s==9)group.push_back(l);}
  shuffle(group.begin()+1,group.end(),rng);group.resize(2+rnd(3));
  vector<int> qi,centers;
  for(int l:group){
    vector<int> p;for(int x=0;x<13;x++){int s=(x+l)%13;if(x!=z&&(s==0||s==1||s==3||s==9))p.push_back(x);}
    if(l)shuffle(p.begin(),p.end(),rng);assert(l||(p[0]==0&&p[1]==1));
    int u=add(1,p[0],p[1]);u=add(1,u,p[2]);qi.push_back(add(0,13+l,u));centers.push_back(13+l);
  }
  auto join=[&](vector<int> v){while(v.size()>1){int a=v.back();v.pop_back();int b=v.back();v.pop_back();v.push_back(add(1,a,b));}return v[0];};
  int c=join(centers),q=join(qi);out.push_back(add(0,c,add(1,z,q)));
  for(int l=0;l<13;l++)if(find(group.begin(),group.end(),l)==group.end()){
    vector<int> p;for(int x=0;x<13;x++){int s=(x+l)%13;if(s==0||s==1||s==3||s==9)p.push_back(x);}
    shuffle(p.begin(),p.end(),rng);int u=add(1,p[0],p[1]);u=add(1,u,p[2]);u=add(1,u,p[3]);out.push_back(add(0,13+l,u));
  }
  join(out);assert(g.size()==65);return g;
}
static void seed_graph() {
  auto raw=(ng>=65&&rnd(2))?nonstar_baseline():baseline();int root=raw.size()-1;
  if(ng==63) {
    int d;do{d=1+rnd(51);}while(raw[d].op!=1);
    int bypass=rnd(2)?raw[d].a:raw[d].b;
    raw.erase(raw.begin()+d);
    for(auto &g:raw)for(int *p:{&g.a,&g.b}) {
      if(*p==26+d)*p=bypass;
      if(*p>26+d)--*p;
    }
    root=62;
  } else {
    while(int(raw.size())<ng) {
      int lim=26+raw.size(),a,b;
      do{a=rnd(lim);}while(a==26+root);
      do{b=rnd(lim);}while(b==26+root);
      raw.push_back({rnd(2),a,b});
    }
  }
  // Random topological order interleaves inactive and useful gates; first/root are fixed.
  vector<int> map(26+ng,-1);iota(map.begin(),map.begin()+26,0);
  gates.clear();vector<bool> done(ng,false);
  for(int k=0;k<ng;k++) {
    int pick;
    if(k==0)pick=0;
    else if(k==ng-1)pick=root;
    else {
      vector<int> avail;
      for(int i=1;i<ng;i++)if(i!=root&&!done[i]&&map[raw[i].a]>=0&&map[raw[i].b]>=0)avail.push_back(i);
      assert(!avail.empty());pick=avail[rnd(avail.size())];
    }
    assert(map[raw[pick].a]>=0&&map[raw[pick].b]>=0);
    map[26+pick]=26+k;done[pick]=true;
    gates.push_back({raw[pick].op,map[raw[pick].a],map[raw[pick].b]});
  }
}
int main(int argc,char**argv) {
  if(argc!=6){cerr<<"usage: data seed seconds genotype checkpoint\n";return 2;}
  uint64_t seed=stoull(argv[2]);rng.seed(seed);double seconds=stod(argv[3]);ng=stoi(argv[4]);checkpoint=argv[5];
  assert(ng==63||(ng>=64&&ng<=MAXG));
  ifstream f(argv[1]);f>>nrows>>nw;assert(nw<=MAXW&&nrows>=52);
  for(int i=0;i<26;i++)for(int w=0;w<nw;w++)f>>words[i][w];
  assert(f.good());
  auto start=chrono::steady_clock::now();int restarts=0;
  while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds) {
    seed_graph();Score cur=eval();int posWeight=1<<rnd(5);
    double baseTemp=array<double,8>{0.2,0.5,1,2,4,8,16,32}[rnd(8)];
    auto energy=[&](const Score&s){return 32.0*(posWeight*s.fn+s.fp)+s.active;};
    if(cur.fn+cur.fp==0&&cur.active<bestCorrect){bestCorrect=cur.active;save(cur,seed);}
    for(int j=0;j<150000;j++) {
      if((j&8191)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
      ++iterations;int i=1+rnd(ng-1);Gate old=gates[i];int kind=rnd(100);
      if(kind<43)gates[i].a=rnd(26+i);
      else if(kind<86)gates[i].b=rnd(26+i);
      else if(kind<96)gates[i].op^=1;
      else gates[i]={rnd(2),rnd(26+i),rnd(26+i)};
      Score cand=eval(i);double delta=energy(cand)-energy(cur);
      double temp=baseTemp*(0.1+0.9*(1.0-double(j%30000)/30000));
      bool accept=delta<=0||generate_canonical<double,53>(rng)<exp(-delta/temp);
      if(accept)cur=cand;
      else {gates[i]=old;eval(i);}
      if(cur.fn+cur.fp<bestWrong)bestWrong=cur.fn+cur.fp;
      if(cur.fn+cur.fp==0&&cur.active<bestCorrect) {
        bestCorrect=cur.active;save(cur,seed);
        cout<<"{\"event\":\"improved\",\"iterations\":"<<iterations<<",\"active\":"<<cur.active<<"}\n"<<flush;
        if(cur.active<=63)return 0;
      }
    }
    ++restarts;
    cout<<"{\"restart\":"<<restarts<<",\"iterations\":"<<iterations<<",\"fn\":"<<cur.fn
        <<",\"fp\":"<<cur.fp<<",\"active\":"<<cur.active<<",\"best_correct\":"<<bestCorrect
        <<",\"best_wrong\":"<<bestWrong<<"}\n"<<flush;
  }
  cout<<"{\"done\":true,\"iterations\":"<<iterations<<",\"best_correct\":"<<bestCorrect<<",\"best_wrong\":"<<bestWrong<<"}\n";
  return bestCorrect<=63?0:1;
}
