#include <bits/stdc++.h>
#include <sys/resource.h>
using namespace std;
using U=uint64_t;
struct G{int op,a,b;};
struct C{vector<G>g;array<int,3>out;int err=0,cost=0;double score=0;};
int ni,nr,nw,no,limit,ng=100;vector<pair<int,int>> edges;vector<vector<U>>ins,care,want;vector<U>trainMask;mt19937_64 rng;uint64_t evals=0;
int ri(int n){return rng()%n;}
double ur(){return (rng()>>11)*0x1.0p-53;}
void assess(C &c){
 vector<vector<U>> val(ni+ng,vector<U>(nw));for(int i=0;i<ni;i++)val[i]=ins[i];
 vector<int> alias(ni+ng);iota(alias.begin(),alias.end(),0);
 for(int i=0;i<ng;i++){
  int a=alias[c.g[i].a],b=alias[c.g[i].b];
  if(a==b)alias[ni+i]=a;
  else{
   auto absorb=[&](int u,int v){if(v<ni)return false;G h=c.g[v-ni];return h.op!=c.g[i].op&&(alias[h.a]==u||alias[h.b]==u);};
   if(absorb(a,b))alias[ni+i]=a;else if(absorb(b,a))alias[ni+i]=b;
  }
  for(int k=0;k<nw;k++)val[ni+i][k]=c.g[i].op?(val[a][k]&val[b][k]):(val[a][k]|val[b][k]);
 }
 c.err=0;for(int o=0;o<no;o++)for(int k=0;k<nw;k++)c.err+=__builtin_popcountll((val[c.out[o]][k]^want[o][k])&care[o][k]);
 vector<bool> use(ng);function<void(int)>visit=[&](int w){w=alias[w];if(w<ni||use[w-ni])return;use[w-ni]=true;visit(c.g[w-ni].a);visit(c.g[w-ni].b);};
 for(int w:c.out)visit(w);use[0]=true;c.cost=count(use.begin(),use.end(),true);
 int trainerr=0;for(int o=0;o<no;o++)for(int k=0;k<nw;k++)trainerr+=__builtin_popcountll((val[c.out[o]][k]^want[o][k])&care[o][k]&trainMask[k]);
 int fn=__builtin_popcountll((~val[c.out[0]][0])&((1ULL<<45)-1));c.score=trainerr+49.0*fn+10.0*max(0,c.cost-limit)+.001*c.cost;evals++;
}
void save(C c,string path){
 vector<int>alias(ni+ng);iota(alias.begin(),alias.end(),0);
 for(int i=0;i<ng;i++){
  int a=alias[c.g[i].a],b=alias[c.g[i].b];c.g[i].a=a;c.g[i].b=b;
  if(a==b)alias[ni+i]=a;
  else{auto ab=[&](int u,int v){return v>=ni&&c.g[v-ni].op!=c.g[i].op&&(c.g[v-ni].a==u||c.g[v-ni].b==u);};if(ab(a,b))alias[ni+i]=a;else if(ab(b,a))alias[ni+i]=b;}
 }
 vector<bool>use(ng);function<void(int)>visit=[&](int w){w=alias[w];if(w<ni||use[w-ni])return;use[w-ni]=true;visit(c.g[w-ni].a);visit(c.g[w-ni].b);};for(int w:c.out)visit(w);use[0]=true;
 vector<int>idx(ni+ng);iota(idx.begin(),idx.end(),0);int ct=ni;for(int i=0;i<ng;i++)if(use[i])idx[ni+i]=ct++;
 ofstream f(path);f<<"{\"inputs\":"<<ni<<",\"errors\":"<<c.err<<",\"active\":"<<c.cost<<",\"gates\":[";bool first=true;
 for(int i=0;i<ng;i++)if(use[i]){if(!first)f<<",";first=false;f<<"["<<c.g[i].op<<","<<idx[alias[c.g[i].a]]<<","<<idx[alias[c.g[i].b]]<<"]";}
 f<<"],\"outputs\":[";for(int o=0;o<no;o++){if(o)f<<",";f<<idx[alias[c.out[o]]];}f<<"]}\n";
}
G guided(C const &c,int i){
 vector<vector<U>>v(ni+ng,vector<U>(nw));for(int a=0;a<ni;a++)v[a]=ins[a];
 auto tail=[&](int from){for(int j=from;j<ng;j++)for(int k=0;k<nw;k++)v[ni+j][k]=c.g[j].op?(v[c.g[j].a][k]&v[c.g[j].b][k]):(v[c.g[j].a][k]|v[c.g[j].b][k]);};
 tail(0);auto old=v[ni+i];array<vector<U>,3>lo,delta;
 fill(v[ni+i].begin(),v[ni+i].end(),0);tail(i+1);for(int o=0;o<3;o++)lo[o]=v[c.out[o]];
 fill(v[ni+i].begin(),v[ni+i].end(),~U(0));tail(i+1);bool visible=false;
 for(int o=0;o<3;o++){delta[o].resize(nw);for(int k=0;k<nw;k++){delta[o][k]=v[c.out[o]][k]^lo[o][k];visible|=(delta[o][k]&care[o][k])!=0;}}
 if(!visible)return G{ri(2),ri(ni+i),ri(ni+i)};
 G best=c.g[i];int besterr=INT_MAX,bestnovel=1,seen=1;
 for(int a=0;a<ni+i;a++)for(int b=a;b<ni+i;b++)for(int op=0;op<2;op++){
  int err=0;bool diff=false;
  for(int k=0;k<nw;k++){U z=op?(v[a][k]&v[b][k]):(v[a][k]|v[b][k]);diff|=z!=old[k];for(int o=0;o<3;o++){U out=lo[o][k]|(z&delta[o][k]);err+=__builtin_popcountll((out^want[o][k])&care[o][k]&trainMask[k]);if(o==0&&k==0)err+=49*__builtin_popcountll((~out)&((1ULL<<45)-1));}if(err>besterr)break;}
  if(err>besterr)continue;int novelty=diff?0:1;
  if(err<besterr||(err==besterr&&novelty<bestnovel)){besterr=err;bestnovel=novelty;best={op,a,b};seen=1;}
  else if(err==besterr&&novelty==bestnovel&&ri(++seen)==0)best={op,a,b};
 }
 return best;
}
C randomized_seed(){
 C c;auto add=[&](int op,int a,int b){int w=ni+c.g.size();c.g.push_back({op,a,b});return w;};
 add(0,0,1);int aout=add(0,ni,3);int bout=add(0,15,16);bout=add(0,bout,18);
 vector<int>ps{aout},ls{bout};for(int i=0;i<12;i++)if(i!=0&&i!=1&&i!=3)ps.push_back(i);for(int i=12;i<24;i++)if(i!=15&&i!=16&&i!=18)ls.push_back(i);
 auto reduce=[&](vector<int> v){while(v.size()>1){int j=ri(v.size()),a=v[j];v.erase(v.begin()+j);j=ri(v.size());int b=v[j];v.erase(v.begin()+j);v.push_back(add(0,a,b));}return v[0];};
 int x=reduce(ps),y=reduce(ls);c.out={add(1,x,y),aout,bout};assert(c.g.size()==23);
 while((int)c.g.size()<ng){int w=ni+c.g.size();c.g.push_back({ri(2),ri(w),ri(w)});}return c;
}
void topo(C &c){
 vector<int>mp(ni+ng,-1);iota(mp.begin(),mp.begin()+ni,0);vector<bool>done(ng);vector<G> g;
 for(int k=0;k<ng;k++){int pick=0;if(k){vector<int> av;for(int i=1;i<ng;i++)if(!done[i]&&mp[c.g[i].a]>=0&&mp[c.g[i].b]>=0)av.push_back(i);assert(!av.empty());pick=av[ri(av.size())];}
  g.push_back({c.g[pick].op,mp[c.g[pick].a],mp[c.g[pick].b]});mp[ni+pick]=ni+k;done[pick]=true;
 }
 for(int &o:c.out)o=mp[o];c.g=move(g);
}
int main(int argc,char**argv){
 if(argc!=5){cerr<<"usage: geometry-core-cgp DATA SEED SECONDS OUTPREFIX\n";return 2;}
 rlimit cap{0,0};setrlimit(RLIMIT_CORE,&cap);cap={2ULL<<30,2ULL<<30};setrlimit(RLIMIT_AS,&cap);
 rng.seed(stoull(argv[2]));int seconds=stoi(argv[3]);if(seconds>120)return 2;cap={rlim_t(seconds+2),rlim_t(seconds+3)};setrlimit(RLIMIT_CPU,&cap);
 ifstream in(argv[1]);in>>ni>>nr>>nw>>no>>limit;assert(no==3&&ni==24);ins.assign(ni,vector<U>(nw));care.assign(no,vector<U>(nw));want=care;
 for(auto *m:{&ins,&care,&want})for(auto &r:*m)for(U &x:r)in>>x;
 int nseed;in>>nseed;C base;base.g.resize(ng);for(int i=0;i<nseed;i++)in>>base.g[i].op>>base.g[i].a>>base.g[i].b;for(auto &o:base.out)in>>o;int ne;in>>ne;for(int k=0;k<ne;k++){int a,b;in>>a>>b;edges.push_back({a,b});}
 for(int i=nseed;i<ng;i++)base.g[i]={ri(2),ri(ni+i),ri(ni+i)};
 trainMask.assign(nw,~U(0));vector<int>curriculum;for(int i=45;i<nr;i++)curriculum.push_back(i);shuffle(curriculum.begin(),curriculum.end(),rng);base=randomized_seed();assess(base);C best=base;save(best,string(argv[4])+"-best.json");cerr<<"initial err="<<base.err<<" cost="<<base.cost<<" score="<<base.score<<"\n";
 auto start=chrono::steady_clock::now();int restarts=0;double last=0;C cur=base;int oldstage=-1;double bestFull=1e99;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();int stage=min(11,int(elapsed/10));if(stage!=oldstage){oldstage=stage;fill(trainMask.begin(),trainMask.end(),0);for(int i=0;i<45;i++)trainMask[i/64]|=U(1)<<(i%64);for(int i=45;i<nr;i++){bool left=true,right=true;for(int j=0;j<24;j++){bool v=(ins[j][i/64]>>(i%64))&1;left&=v==(j<12);right&=v==(j>=12);}if(left||right)trainMask[i/64]|=U(1)<<(i%64);}for(int j=0;j<min(int(curriculum.size()),stage*60);j++){int i=curriculum[j];trainMask[i/64]|=U(1)<<(i%64);}assess(cur);best=cur;cerr<<"stage="<<stage<<" full="<<cur.err<<" cost="<<cur.cost<<" score="<<cur.score<<"\n";}double phase=fmod(elapsed,10.0)/10.0;double temp=8.0*pow(.01,phase)+.04;
  if(elapsed-last>10){restarts++;last=elapsed;cur=best;topo(cur);assess(cur);cerr<<"time="<<elapsed<<" evals="<<evals<<" best="<<best.err<<","<<best.cost<<" current="<<cur.err<<","<<cur.cost<<"\n";}
  C q=cur;int nm=1+(ri(12)==0?ri(4)+1:0);
  if(evals%80==0){int i=1+ri(ng-1);q.g[i]=guided(cur,i);}else for(int k=0;k<nm;k++){
   if(ri(15)==0){int o=ri(no);q.out[o]=ri(ni+ng);continue;}
   int i=1+ri(ng-1),which=ri(4);
   if(which==0)q.g[i].op^=1;else if(which==1)q.g[i].a=ri(ni+i);else if(which==2)q.g[i].b=ri(ni+i);
   else {int prior=ri(i);q.g[i]=q.g[prior];}
  }
  assess(q);double delta=q.score-cur.score;
  if(delta<=0||ur()<exp(-delta/temp))cur=move(q);
  if(cur.score<best.score){best=cur;save(best,string(argv[4])+"-best.json");cerr<<"improved evals="<<evals<<" err="<<best.err<<" cost="<<best.cost<<" score="<<best.score<<"\n";}
  double fs=cur.err+10.0*max(0,cur.cost-limit)+.001*cur.cost;if(fs<bestFull){bestFull=fs;save(cur,string(argv[4])+"-bestfull.json");cerr<<"full_improved="<<cur.err<<","<<cur.cost<<"\n";}
  if(cur.err==0&&cur.cost<=limit){save(cur,string(argv[4])+"-FOUND.json");cerr<<"FOUND\n";return 0;}
 }
 cerr<<"finished evals="<<evals<<" best_err="<<best.err<<" best_cost="<<best.cost<<" restarts="<<restarts<<"\n";return 0;
}
