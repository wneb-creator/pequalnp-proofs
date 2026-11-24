#include "data.hpp"
constexpr int SZ=61, NN=25+SZ;
using Bits=array<uint64_t,W>;
struct G { int op,a,b; };
struct C { array<G,SZ> g; int f=NN-1,q=NN-2; int score=INT_MAX; };
Bits fp{},fn{},qp{},qn{};
array<Bits,NN> val;
mt19937_64 rng(37102215);
int rnd(int n) { return rng()%n; }
void setbit(Bits &b,int i) {b[i/64]|=uint64_t(1)<<(i%64);}
int mismatch(const Bits &v,const Bits &pos,const Bits &neg) {int s=0; for(int j=0;j<W;j++)s+=__builtin_popcountll((v[j]&neg[j])|(~v[j]&pos[j]));return s;}
void eval(C &c) {
 for(int i=0;i<SZ;i++){
  auto [op,a,b]=c.g[i];
  for(int j=0;j<W;j++)val[25+i][j]=op?(val[a][j]|val[b][j]):(val[a][j]&val[b][j]);
 }
 int fs=INT_MAX,qs=INT_MAX;
 for(int i=0;i<NN;i++) {
  int f=mismatch(val[i],fp,fn),q=mismatch(val[i],qp,qn);
  if(f<fs){fs=f;c.f=i;}
  if(q<qs){qs=q;c.q=i;}
 }
 c.score=fs+qs;
}
vector<int> active(const C &c){
 vector<int> a; array<bool,NN> used{};used[c.f]=used[c.q]=true;
 for(int i=SZ-1;i>=0;i--)if(used[25+i]){a.push_back(i);used[c.g[i].a]=used[c.g[i].b]=true;}
 return a;
}
C seed() {
 vector<G> g;
 auto add=[&](int op,int a,int b){g.push_back({op,a,b});return 25+(int)g.size()-1;};
 vector<int> ps(13);for(int i=0;i<13;i++)ps[i]=i;shuffle(ps.begin(),ps.end(),rng);
 vector<int> roots;
 for(int p:ps){
  if(p==12){vector<int>d={12,13,15,21};shuffle(d.begin(),d.end(),rng);int a=add(1,d[0],d[1]);int b=add(1,d[2],d[3]);add(1,a,b);continue;}
  vector<int> ns(NEIGH[p],NEIGH[p]+4);shuffle(ns.begin(),ns.end(),rng);int a=add(1,ns[0],ns[1]),b=add(1,ns[2],ns[3]);int z=add(1,a,b);roots.push_back(add(0,p,z));
 }
 while(roots.size()>1){int a=roots.back();roots.pop_back();int b=roots.back();roots.pop_back();roots.insert(roots.begin()+rnd(roots.size()+1),add(1,a,b));}
 int k=rnd(62);int replacement=rnd(2)?g[k].a:g[k].b;
 g.erase(g.begin()+k);
 for(auto &z:g) for(int *p:{&z.a,&z.b}){if(*p==25+k)*p=replacement;if(*p>25+k)--*p;}
 C c;copy(g.begin(),g.end(),c.g.begin());eval(c);return c;
}
void save(const C &c,const string &path){ofstream o(path);o<<"score "<<c.score<<" f "<<c.f<<" q "<<c.q<<"\n";for(int i=0;i<SZ;i++)o<<25+i<<" "<<(c.g[i].op?"or":"and")<<" "<<c.g[i].a<<" "<<c.g[i].b<<"\n";}

int main(int argc,char**argv) {
 int seconds=argc>1?stoi(argv[1]):900; if(argc>2)rng.seed(stoull(argv[2]));
 for(int i=0;i<25;i++)for(int j=0;j<N;j++)if(ROWS[j]>>i&1)setbit(val[i],j);
 for(int i : ::fpos)setbit(fp,i);for(int i:fneg)setbit(fn,i);for(int i:qpos)setbit(qp,i);for(int i:qneg)setbit(qn,i);
 Bits fullfn=fn,fullqn=qn;auto t0=chrono::steady_clock::now();long long count=0,checks=0;int best=INT_MAX,restarts=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-t0).count()<seconds){
  fn=fullfn;qn=fullqn;C c=seed();if(c.score<best){best=c.score;save(c,"/tmp/oec/pequalnp-pilot-37/circuit_search/best-cegis.txt");cout<<"best full "<<best<<" checks "<<checks<<endl;}
  fn={};qn={};eval(c);restarts++;int stuck=0;
  for(int it=0;it<1000000;it++){
   if(c.score==0){
    eval(c);checks++;
    int exact=mismatch(val[c.f],fp,fullfn)+mismatch(val[c.q],qp,fullqn);
    if(exact<best){best=exact;C w=c;w.score=exact;save(w,"/tmp/oec/pequalnp-pilot-37/circuit_search/best-cegis.txt");cout<<"best full "<<best<<" iterations "<<count<<" checks "<<checks<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;}
    if(exact==0)return 0;
    vector<int>badf,badq;
    for(int i:fneg)if(val[c.f][i/64]>>(i%64)&1)badf.push_back(i);
    for(int i:qneg)if(val[c.q][i/64]>>(i%64)&1)badq.push_back(i);
    if(!badf.empty())setbit(fn,badf[rnd(badf.size())]);
    if(!badq.empty())setbit(qn,badq[rnd(badq.size())]);
    eval(c);stuck=0;
   }
   auto a=active(c);C d=c;int nm=1;while(nm<5&&rnd(4)==0)nm++;
   for(int j=0;j<nm;j++){
    int k=(a.empty()||rnd(10)==0)?rnd(SZ):a[rnd(a.size())];int field=rnd(3);
    if(field==0)d.g[k].op=1-d.g[k].op;
    else if(field==1)d.g[k].a=rnd(25+k);
    else d.g[k].b=rnd(25+k);
   }
   eval(d);count++;
   if(d.score<=c.score){if(d.score<c.score)stuck=0;c=d;}else stuck++;
   if(stuck>100000)break;
   if(count%10000==0&&chrono::duration<double>(chrono::steady_clock::now()-t0).count()>seconds)break;
  }
 }
 cout<<"DONE best full "<<best<<" iterations "<<count<<" restarts "<<restarts<<" rejected candidates "<<checks<<endl;
}
