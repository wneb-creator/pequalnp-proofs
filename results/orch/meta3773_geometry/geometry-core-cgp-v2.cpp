#include <bits/stdc++.h>
#include <sys/resource.h>
using namespace std;
using U=uint64_t;
struct G{int op,a,b;};
struct C{vector<G>g;array<int,3>out;int err=0,cost=0;double score=0;};
int ni,nr,nw,no,limit,ng=100;vector<pair<int,int>> edges;vector<vector<U>>ins,care,want;mt19937_64 rng;uint64_t evals=0;
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
 c.score=c.err+10.0*max(0,c.cost-limit)+.001*c.cost;evals++;
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
C randomized_seed(){
 C c;auto add=[&](int op,int a,int b){int w=ni+c.g.size();c.g.push_back({op,a,b});return w;};
 add(0,0,1);int aout=add(0,ni,3);int bout=add(0,15,16);bout=add(0,bout,18);
 vector<int>points(12);iota(points.begin(),points.end(),0);shuffle(points.begin(),points.end(),rng);vector<int>terms;
 for(int p:points){vector<int> adj;for(auto [i,j]:edges)if(i==p)adj.push_back(j);shuffle(adj.begin(),adj.end(),rng);
  while(adj.size()>1){int j=ri(adj.size());int a=adj[j];adj.erase(adj.begin()+j);j=ri(adj.size());int b=adj[j];adj.erase(adj.begin()+j);adj.push_back(add(0,a,b));}
  terms.push_back(add(1,p,adj[0]));
 }
 while(terms.size()>1){int j=ri(terms.size());int a=terms[j];terms.erase(terms.begin()+j);j=ri(terms.size());int b=terms[j];terms.erase(terms.begin()+j);terms.push_back(add(0,a,b));}
 c.out={terms[0],aout,bout};assert(c.g.size()==60);
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
 assess(base);C best=base;save(best,string(argv[4])+"-best.json");cerr<<"initial err="<<base.err<<" cost="<<base.cost<<" score="<<base.score<<"\n";
 auto start=chrono::steady_clock::now();int restarts=0;double last=0;C cur=base;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();double phase=fmod(elapsed,5.0)/5.0;double temp=4.0*pow(.015,phase)+.03;
  if(elapsed-last>5){restarts++;last=elapsed;cur=(restarts%3)?best:randomized_seed();topo(cur);assess(cur);cerr<<"time="<<elapsed<<" evals="<<evals<<" best="<<best.err<<","<<best.cost<<" current="<<cur.err<<","<<cur.cost<<"\n";}
  C q=cur;int nm=1+(ri(12)==0?ri(4)+1:0);
  for(int k=0;k<nm;k++){
   if(ri(15)==0){int o=ri(no);q.out[o]=ri(ni+ng);continue;}
   int i=1+ri(ng-1),which=ri(4);
   if(which==0)q.g[i].op^=1;else if(which==1)q.g[i].a=ri(ni+i);else if(which==2)q.g[i].b=ri(ni+i);
   else {int prior=ri(i);q.g[i]=q.g[prior];}
  }
  assess(q);double delta=q.score-cur.score;
  if(delta<=0||ur()<exp(-delta/temp))cur=move(q);
  if(cur.score<best.score){best=cur;save(best,string(argv[4])+"-best.json");cerr<<"improved evals="<<evals<<" err="<<best.err<<" cost="<<best.cost<<" score="<<best.score<<"\n";}
  if(cur.err==0&&cur.cost<=limit){save(cur,string(argv[4])+"-FOUND.json");cerr<<"FOUND\n";return 0;}
 }
 cerr<<"finished evals="<<evals<<" best_err="<<best.err<<" best_cost="<<best.cost<<" restarts="<<restarts<<"\n";return 0;
}
