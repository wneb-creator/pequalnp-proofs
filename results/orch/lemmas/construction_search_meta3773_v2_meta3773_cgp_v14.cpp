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
struct Score { int fn,fp,active,unproductive,nested,singletons,essential; };
static constexpr int MAXG=140, MAXW=16;
static uint64_t words[26+MAXG][MAXW];
static int nw,nrows,ng,headType;
static uint64_t singletonMask[MAXW]={};
static mt19937_64 rng;
static vector<Gate> gates;
static vector<Gate> warmSeed;
static int rnd(int n) { return int(rng()%n); }
static uint64_t iterations=0;
static int bestCorrect=100000,bestWrong=100000,bestNear=100000,bestNested=-1,bestUnproductive=100000,bestNearUnproductive=100000;
static vector<vector<Gate>> pool;
static vector<Gate> bestOverGraph;static double bestOverScore=1e100;
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
  int count=0,unproductive=0,nested=0,essential=0;bool hasAnd[MAXG]={};
  for(int i=0;i<ng;i++)if(active[i]) {
    ++count;int a=aliasWire[gates[i].a],b=aliasWire[gates[i].b];
    bool below=(a>=26&&hasAnd[a-26])||(b>=26&&hasAnd[b-26]);
    hasAnd[i]=gates[i].op==0||below;nested+=gates[i].op==0&&below;
    if(gates[i].op==0){bool fires=words[26+i][0]&~pos;for(int w=1;w<nw;w++)fires|=words[26+i][w]!=0;unproductive+=fires;
      if(fires&&aliasWire[26+ng-1]>=26+i){
        uint64_t temp[26+MAXG][MAXW];memcpy(temp,words,sizeof(words));int rt=aliasWire[26+ng-1];
        for(int w=0;w<nw;w++)temp[26+i][w]=(w==nw-1&&nrows%64)?((uint64_t(1)<<(nrows%64))-1):~uint64_t(0);
        for(int k=i+1;26+k<=rt;k++){int aa=aliasWire[gates[k].a],bb=aliasWire[gates[k].b];for(int w=0;w<nw;w++)temp[26+k][w]=gates[k].op?(temp[aa][w]|temp[bb][w]):(temp[aa][w]&temp[bb][w]);}
        bool ca=false,cb=false;for(int w=0;w<nw;w++){uint64_t care=temp[rt][w]^words[rt][w];ca|=(care&words[a][w])!=0;cb|=(care&words[b][w])!=0;}essential+=ca&&cb;
      }
    }
  }
  int singletonErrors=0;for(int w=0;w<nw;w++)singletonErrors+=__builtin_popcountll(words[26+ng-1][w]&singletonMask[w]);
  return {fn,fp,count,unproductive,nested,singletonErrors,essential};
}
static Score context_prune() {
  Score cur=eval();int root=aliasWire[26+ng-1];
  for(int i=0;i<ng;i++){gates[i].a=aliasWire[gates[i].a];gates[i].b=aliasWire[gates[i].b];}
  if(root!=26+ng-1)gates[ng-1]={1,root,root};cur=eval();
  uint64_t target[MAXW];memcpy(target,words[26+ng-1],nw*sizeof(uint64_t));
  for(int i=ng-1;i>0;i--)if(active[i]){
    Gate old=gates[i];for(int child:{old.a,old.b}){
      gates[i]={1,child,child};Score cand=eval(i);
      if(cand.active<=cur.active&&memcmp(target,words[26+ng-1],nw*sizeof(uint64_t))==0){cur=cand;break;}
      gates[i]=old;cur=eval(i);
    }
  }
  return cur;
}
static void save(const Score&s,uint64_t seed,const string&target="") {
  vector<int> remap(26+ng,-1);iota(remap.begin(),remap.begin()+26,0);
  vector<Gate> out;
  for(int i=0;i<ng;i++)if(active[i]) {
    assert(remap[aliasWire[gates[i].a]]>=0&&remap[aliasWire[gates[i].b]]>=0);
    remap[26+i]=26+out.size();out.push_back({gates[i].op,remap[aliasWire[gates[i].a]],remap[aliasWire[gates[i].b]]});
  }
  ofstream f(target.empty()?checkpoint:target);
  f<<"{\"seed\":"<<seed<<",\"iterations\":"<<iterations<<",\"fn\":"<<s.fn
   <<",\"fp\":"<<s.fp<<",\"active\":"<<s.active<<",\"unproductive\":"<<s.unproductive<<",\"essential_bad\":"<<s.essential<<",\"nested\":"<<s.nested<<",\"input_count\":26,\"output\":"
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
static vector<Gate> cnf_baseline() {
  vector<Gate> g;vector<int> out;auto add=[&](int op,int a,int b){int w=26+g.size();g.push_back({op,a,b});return w;};
  int q=1+rnd(12);vector<int> neigh(13,-1);
  auto makeN=[&](int l){vector<int> p;for(int x=0;x<13;x++){int v=(x+l)%13;if(v==0||v==1||v==3||v==9)p.push_back(x);}if(l)shuffle(p.begin(),p.end(),rng);int u=add(1,p[0],p[1]);u=add(1,u,p[2]);return add(1,u,p[3]);};
  int a=13,c=13+q,b=makeN(0),d=makeN(q);
  bool filtered=rnd(2);int v;
  if(filtered){int cd=add(0,c,d),u=add(1,b,cd),p=add(1,a,c);v=add(0,u,p);int filter=add(1,a,d);v=add(0,v,filter);}
  else {int P=add(1,a,c),N=add(1,b,d),X=add(1,a,d),Y=add(1,c,b);v=add(0,P,N);v=add(0,v,X);v=add(0,v,Y);}
  out.push_back(v);
  for(int l=1;l<13;l++)if(l!=q)out.push_back(add(0,13+l,makeN(l)));
  while(out.size()>1){int a=out.back();out.pop_back();int b=out.back();out.pop_back();out.push_back(add(1,a,b));}
  assert(g.size()==(filtered?67:68));return g;
}
static vector<Gate> bad_baseline(int pairs) {
  vector<Gate> g;vector<int> out;auto add=[&](int op,int a,int b){int w=26+g.size();g.push_back({op,a,b});return w;};
  vector<int> remaining(13);iota(remaining.begin(),remaining.end(),0);
  int z=rnd(2)?3:9;vector<int> partners;for(int q=1;q<13;q++){int s=(z+q)%13;if(s==0||s==1||s==3||s==9)partners.push_back(q);}
  int first=partners[rnd(partners.size())];vector<pair<int,int>> blocks{{0,first}};
  remaining.erase(find(remaining.begin(),remaining.end(),0));remaining.erase(find(remaining.begin(),remaining.end(),first));shuffle(remaining.begin(),remaining.end(),rng);
  for(int k=1;k<pairs;k++){int a=remaining.back();remaining.pop_back();int b=remaining.back();remaining.pop_back();blocks.push_back({a,b});}
  auto neighbors=[&](int l,int skip){vector<int> p;for(int x=0;x<13;x++){int s=(x+l)%13;if(x!=skip&&(s==0||s==1||s==3||s==9))p.push_back(x);}if(l)shuffle(p.begin(),p.end(),rng);return p;};
  for(auto [l,q]:blocks){int common=-1;for(int x=0;x<13;x++){int s=(x+l)%13,t=(x+q)%13;if((s==0||s==1||s==3||s==9)&&(t==0||t==1||t==3||t==9))common=x;}assert(common>=0);
    auto u=neighbors(l,common),v=neighbors(q,common);int U=add(1,u[0],u[1]);U=add(1,U,u[2]);int V=add(1,v[0],v[1]);V=add(1,V,v[2]);
    int a=13+l,c=13+q,T=add(0,add(1,U,common),add(1,a,c));int P=add(0,T,add(1,a,common));out.push_back(add(1,P,add(0,c,V)));
  }
  for(int l:remaining){auto p=neighbors(l,-1);int U=add(1,p[0],p[1]);U=add(1,U,p[2]);U=add(1,U,p[3]);out.push_back(add(0,13+l,U));}
  while(out.size()>1){int a=out.back();out.pop_back();int b=out.back();out.pop_back();out.push_back(add(1,a,b));}
  assert(int(g.size())==64+2*pairs);return g;
}
static vector<Gate> bad_pencil_baseline() {
  vector<Gate> g;vector<int> out;auto add=[&](int op,int a,int b){int w=26+g.size();g.push_back({op,a,b});return w;};
  int z=rnd(2)?3:9;vector<int> group{0};for(int q=1;q<13;q++){int s=(q+z)%13;if(s==0||s==1||s==3||s==9)group.push_back(q);}shuffle(group.begin()+1,group.end(),rng);group.resize(2+rnd(3));
  vector<int> U,A;for(int l:group){vector<int> p;for(int x=0;x<13;x++){int s=(l+x)%13;if(x!=z&&(s==0||s==1||s==3||s==9))p.push_back(x);}if(l)shuffle(p.begin(),p.end(),rng);int u=add(1,p[0],p[1]);u=add(1,u,p[2]);U.push_back(u);A.push_back(13+l);}
  int a=A[0];for(size_t k=1;k<A.size();k++)a=add(1,a,A[k]);int t=add(0,a,add(1,z,U[0]));int p=add(0,t,add(1,A[0],z));out.push_back(p);for(size_t k=1;k<A.size();k++)out.push_back(add(0,A[k],U[k]));
  for(int l=1;l<13;l++)if(find(group.begin(),group.end(),l)==group.end()){vector<int> p;for(int x=0;x<13;x++){int s=(l+x)%13;if(s==0||s==1||s==3||s==9)p.push_back(x);}shuffle(p.begin(),p.end(),rng);int u=add(1,p[0],p[1]);u=add(1,u,p[2]);u=add(1,u,p[3]);out.push_back(add(0,13+l,u));}
  while(out.size()>1){int a=out.back();out.pop_back();int b=out.back();out.pop_back();out.push_back(add(1,a,b));}assert(g.size()==66);return g;
}
static void seed_graph(int unproductiveSeed=0) {
  bool warm=!warmSeed.empty()&&rnd(2);
  auto raw=warm?warmSeed:(unproductiveSeed?(unproductiveSeed==1&&rnd(2)?bad_pencil_baseline():bad_baseline(unproductiveSeed)):((ng>=65&&rnd(2))?nonstar_baseline():baseline()));int root=raw.size()-1;
  if(headType&&!warm) {
    for(auto &g:raw){if(g.a>=26)++g.a;if(g.b>=26)++g.b;}
    Gate lead=headType==1?Gate{0,0,13}:(headType==2?Gate{1,0,13}:Gate{1,2,13});
    raw.insert(raw.begin(),lead);++root;
  }
  if(ng==63) {
    while(int(raw.size())>ng) {
      int d;do{d=1+rnd(raw.size()-2);}while(raw[d].op!=1);
      int bypass=rnd(2)?raw[d].a:raw[d].b;
      raw.erase(raw.begin()+d);
      for(auto &g:raw)for(int *p:{&g.a,&g.b}) {
        if(*p==26+d)*p=bypass;
        if(*p>26+d)--*p;
      }
      --root;
    }
  } else {
    while(int(raw.size())<ng) {
      int lim=26+raw.size(),a,b;
      do{a=rnd(lim);}while(a==26+root);
      do{b=rnd(lim);}while(b==26+root);
      raw.push_back({rnd(2),a,b});
    }
  }
  assert(int(raw.size()) == ng);
  // Random topological order interleaves inactive and useful gates; first/root are fixed.
  vector<int> map(26+ng,-1);iota(map.begin(),map.begin()+26,0);
  gates.clear();vector<bool> done(ng,false);
  bool lateExtras=rnd(2);
  for(int k=0;k<ng;k++) {
    int pick;
    if(k==0)pick=0;
    else if(k==ng-1)pick=root;
    else {
      vector<int> avail;
      for(int i=1;i<ng;i++)if(i!=root&&!done[i]&&map[raw[i].a]>=0&&map[raw[i].b]>=0)avail.push_back(i);
      if(lateExtras){vector<int> base;for(int i:avail)if(i<root)base.push_back(i);if(!base.empty())avail=base;}
      assert(!avail.empty());pick=avail[rnd(avail.size())];
    }
    assert(map[raw[pick].a]>=0&&map[raw[pick].b]>=0);
    map[26+pick]=26+k;done[pick]=true;
    gates.push_back({raw[pick].op,map[raw[pick].a],map[raw[pick].b]});
  }
}
static Gate guided(int i,int posWeight,const Score&cur) {
  uint64_t low[MAXW],high[MAXW],care[MAXW],oldval[MAXW],val[MAXW];
  for(int w=0;w<nw;w++)oldval[w]=words[26+i][w];
  auto tail=[&](){for(int j=i+1;j<ng;j++)for(int w=0;w<nw;w++)words[26+j][w]=gates[j].op?(words[gates[j].a][w]|words[gates[j].b][w]):(words[gates[j].a][w]&words[gates[j].b][w]);};
  for(int w=0;w<nw;w++)words[26+i][w]=0;tail();
  for(int w=0;w<nw;w++)low[w]=words[26+ng-1][w];
  for(int w=0;w<nw;w++)words[26+i][w]=(w==nw-1&&nrows%64)?((uint64_t(1)<<(nrows%64))-1):~uint64_t(0);tail();
  bool visible=false;
  for(int w=0;w<nw;w++){high[w]=words[26+ng-1][w];care[w]=high[w]^low[w];visible|=care[w]!=0;}
  eval(i);
  if(!visible)return Gate{rnd(2),rnd(26+i),rnd(26+i)};
  Gate best=gates[i];int besterr=posWeight*(cur.fn+cur.singletons)+cur.fp,bestnovel=1,seen=1;
  const uint64_t pos=(uint64_t(1)<<52)-1;
  for(int a=0;a<26+i;a++)if(aliasWire[a]==a)for(int b=a;b<26+i;b++)if(aliasWire[b]==b)for(int op=0;op<2;op++) {
    int err=0;bool diff=false;
    for(int w=0;w<nw;w++) {
      val[w]=op?(words[a][w]|words[b][w]):(words[a][w]&words[b][w]);
      diff|=val[w]!=oldval[w];uint64_t out=low[w]|(val[w]&care[w]);
      if(w==0)err=posWeight*__builtin_popcountll(~out&pos)+__builtin_popcountll(out&~pos);
      else err+=__builtin_popcountll(out);
      err+=posWeight*__builtin_popcountll(out&singletonMask[w]);
      if(err>besterr)break;
    }
    if(err>besterr)continue;
    int novel=diff?0:1;
    if(err<besterr||(err==besterr&&novel<bestnovel)){besterr=err;bestnovel=novel;best={op,a,b};seen=1;}
    else if(err==besterr&&novel==bestnovel&&rnd(++seen)==0)best={op,a,b};
  }
  return best;
}
static bool guided_two(int posWeight,int minBad,Score &cur) {
  bool rawActive[MAXG]={};vector<int> stack{ng-1};
  while(!stack.empty()){int k=stack.back();stack.pop_back();if(rawActive[k])continue;rawActive[k]=true;for(int w:{gates[k].a,gates[k].b})if(w>=26)stack.push_back(w-26);}
  vector<int> targets;for(int i=2;i<ng;i++)if(rawActive[i])targets.push_back(i);if(targets.empty())return false;
  int i=targets[rnd(targets.size())];vector<int> free;for(int j=1;j<i;j++)if(!rawActive[j])free.push_back(j);if(free.empty())return false;
  int j=rnd(3)?free.back():free[rnd(free.size())],lim=26+j;
  Gate oldj=gates[j],oldi=gates[i];uint64_t low[MAXW],care[MAXW];
  auto tail=[&](){for(int k=i+1;k<ng;k++)for(int w=0;w<nw;w++)words[26+k][w]=gates[k].op?(words[gates[k].a][w]|words[gates[k].b][w]):(words[gates[k].a][w]&words[gates[k].b][w]);};
  for(int w=0;w<nw;w++)words[26+i][w]=0;tail();for(int w=0;w<nw;w++)low[w]=words[26+ng-1][w];
  for(int w=0;w<nw;w++)words[26+i][w]=(w==nw-1&&nrows%64)?((uint64_t(1)<<(nrows%64))-1):~uint64_t(0);tail();
  bool visible=false;for(int w=0;w<nw;w++){care[w]=low[w]^words[26+ng-1][w];visible|=care[w]!=0;}eval(i);if(!visible)return false;
  vector<int> prefix;for(int a=0;a<lim;a++)if(aliasWire[a]==a)prefix.push_back(a);
  const uint64_t pos=(uint64_t(1)<<52)-1;struct Pair{Gate first,second;};vector<Pair> choices;int best=posWeight*(cur.fn+cur.singletons)+cur.fp,seen=0;
  for(int a:prefix)for(int b:prefix)if(a<=b)for(int op=0;op<2;op++) {
    uint64_t pair[MAXW];for(int w=0;w<nw;w++)pair[w]=op?(words[a][w]|words[b][w]):(words[a][w]&words[b][w]);
    for(int c:prefix)for(int last=0;last<2;last++) {
      int err=0;for(int w=0;w<nw;w++){uint64_t v=last?(pair[w]|words[c][w]):(pair[w]&words[c][w]);uint64_t out=low[w]|(v&care[w]);err+=w?__builtin_popcountll(out):posWeight*__builtin_popcountll(~out&pos)+__builtin_popcountll(out&~pos);err+=posWeight*__builtin_popcountll(out&singletonMask[w]);if(err>best)break;}
      if(err>best)continue;if(err<best){best=err;choices.clear();seen=0;}++seen;Pair q{{op,a,b},{last,26+j,c}};
      if(choices.size()<48)choices.push_back(q);else {int at=rnd(seen);if(at<48)choices[at]=q;}
    }
  }
  if(choices.empty())return false;
  Score chosen=cur;Pair winner{oldj,oldi};bool found=false;int tie=0;
  for(auto q:choices){gates[j]=q.first;gates[i]=q.second;Score t=eval(j);int err=posWeight*(t.fn+t.singletons)+t.fp,oldErr=posWeight*(chosen.fn+chosen.singletons)+chosen.fp;
    if(t.essential<minBad)continue;
    if(err<oldErr||(err==oldErr&&t.active<chosen.active)){chosen=t;winner=q;found=true;tie=1;}
    else if(err==oldErr&&t.active==chosen.active&&rnd(++tie)==0){chosen=t;winner=q;found=true;}
  }
  gates[j]=winner.first;gates[i]=winner.second;cur=eval(j);return found;
}
int main(int argc,char**argv) {
  if(argc!=6&&argc!=7){cerr<<"usage: data seed seconds genotype checkpoint [warm-seed]\n";return 2;}
  uint64_t seed=stoull(argv[2]);headType=seed%4;rng.seed(seed);double seconds=stod(argv[3]);ng=stoi(argv[4]);checkpoint=argv[5];
  assert(ng==63||(ng>=64&&ng<=MAXG));
  ifstream f(argv[1]);f>>nrows>>nw;assert(nw<=MAXW&&nrows>=52);
  for(int i=0;i<26;i++)for(int w=0;w<nw;w++)f>>words[i][w];
  assert(f.good());
  if(nrows==782)for(int row=756;row<782;row++)singletonMask[row/64]|=uint64_t(1)<<(row%64);
  if(argc==7){ifstream wf(argv[6]);int count;wf>>count;assert(count>=1&&count<=ng);for(int i=0;i<count;i++){Gate g;wf>>g.op>>g.a>>g.b;assert((g.op==0||g.op==1)&&g.a>=0&&g.b>=0&&g.a<26+i&&g.b<26+i);warmSeed.push_back(g);}assert(wf.good());}
  auto start=chrono::steady_clock::now();int restarts=0;
  while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds) {
    int requireUnproductive=1;
    if(!bestOverGraph.empty()&&rnd(2))gates=bestOverGraph;else seed_graph(requireUnproductive);
    Score cur=context_prune();
    if(cur.essential<requireUnproductive){seed_graph(requireUnproductive);cur=context_prune();}
    int posWeight=1<<rnd(8);int mode=rnd(4);
    double baseTemp=array<double,8>{0.2,0.5,1,2,4,8,16,32}[rnd(8)];
    if(mode)baseTemp*=0.125;
    auto energy=[&](const Score&s){if(mode==3)return 100000.0*(posWeight*(s.fn+s.singletons)+s.fp)+s.active;return mode?(posWeight*(s.fn+s.singletons)+s.fp)+(mode==1?10.0:3.0)*max(0,s.active-63)+0.01*s.active:32.0*(posWeight*(s.fn+s.singletons)+s.fp)+s.active;};
    if(cur.fn+cur.fp==0&&cur.active<bestCorrect){bestCorrect=cur.active;save(cur,seed);if(bestCorrect<=63)return 0;}
    for(int j=0;j<150000;j++) {
      if((j&8191)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
      ++iterations;if(j%5000==4999){Score clean=context_prune();cur=clean;}if(j%3000==2999)guided_two(posWeight,requireUnproductive,cur);int i=1+rnd(ng-1);Gate old=gates[i];int kind=rnd(100);
      if(j%(mode==3?8:80)==0)gates[i]=guided(i,posWeight,cur);
      else if(kind<43)gates[i].a=rnd(26+i);
      else if(kind<86)gates[i].b=rnd(26+i);
      else if(kind<96)gates[i].op^=1;
      else gates[i]={rnd(2),rnd(26+i),rnd(26+i)};
      Score cand=eval(i);double delta=energy(cand)-energy(cur);
      double temp=baseTemp*(0.1+0.9*(1.0-double(j%30000)/30000));
      bool accept=(cand.essential>=requireUnproductive)&&(delta<=0||generate_canonical<double,53>(rng)<exp(-delta/temp));
      if(accept)cur=cand;
      else {gates[i]=old;eval(i);}
      if(cur.fn+cur.fp<bestWrong)bestWrong=cur.fn+cur.fp;
      double overScore=cur.fp+10.0*max(0,cur.active-63);
      if(cur.fn==0&&cur.singletons==0&&overScore<bestOverScore){bestOverScore=overScore;bestOverGraph=gates;save(cur,seed,checkpoint+".over");cout<<"{\"event\":\"over\",\"fp\":"<<cur.fp<<",\"active\":"<<cur.active<<"}\n"<<flush;}
      if(cur.fn+cur.fp==0&&cur.essential>0&&cur.active<bestUnproductive) {
        bestUnproductive=cur.active;save(cur,seed,checkpoint+".unproductive");
        cout<<"{\"event\":\"unproductive\",\"active\":"<<cur.active<<",\"count\":"<<cur.unproductive<<"}\n"<<flush;
      }
      if(cur.active<=63&&cur.essential>0&&cur.fn+cur.fp<bestNearUnproductive) {
        bestNearUnproductive=cur.fn+cur.fp;save(cur,seed,checkpoint+".near-unproductive");
        cout<<"{\"event\":\"near_unproductive\",\"errors\":"<<bestNearUnproductive<<",\"active\":"<<cur.active<<"}\n"<<flush;
      }
      if(j%4096==0&&cur.fn+cur.fp<=4&&cur.active<=69) {
        if(pool.size()<64)pool.push_back(gates);else pool[rnd(pool.size())]=gates;
      }
      if(cur.active<=63&&cur.fn+cur.fp<=bestNear) {
        bool hasAnd[MAXG]={};int nested=0;
        for(int k=0;k<ng;k++)if(active[k]) {
          int a=aliasWire[gates[k].a],b=aliasWire[gates[k].b];
          bool below=(a>=26&&hasAnd[a-26])||(b>=26&&hasAnd[b-26]);
          nested+=gates[k].op==0&&below;hasAnd[k]=gates[k].op==0||below;
        }
        if(cur.fn+cur.fp<bestNear||nested>bestNested) {
          bestNear=cur.fn+cur.fp;bestNested=nested;save(cur,seed,checkpoint+".near");
          cout<<"{\"event\":\"near\",\"errors\":"<<bestNear<<",\"nested\":"<<nested<<",\"active\":"<<cur.active<<"}\n"<<flush;
        }
      }
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
