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
 vector<int> ps(12);for(int i=0;i<12;i++)ps[i]=i;shuffle(ps.begin(),ps.end(),rng);
 vector<int> roots;
 for(int p:ps){vector<int> ns(NEIGH[p],NEIGH[p]+4);shuffle(ns.begin(),ns.end(),rng);int a=add(1,ns[0],ns[1]),b=add(1,ns[2],ns[3]);int z=add(1,a,b);roots.push_back(add(0,p,z));}
 while(roots.size()>1){int a=roots.back();roots.pop_back();int b=roots.back();roots.pop_back();roots.insert(roots.begin()+rnd(roots.size()+1),add(1,a,b));}
 vector<int>d={12,13,15,21};shuffle(d.begin(),d.end(),rng);int a=add(1,d[0],d[1]);int b=add(1,d[2],d[3]);add(1,a,b);
 // Remove an arbitrary gate and bypass it with one of its arguments.
 int k=rnd(62);int replacement=rnd(2)?g[k].a:g[k].b;
 g.erase(g.begin()+k);
 for(auto &z:g) for(int *p:{&z.a,&z.b}){if(*p==25+k)*p=replacement;if(*p>25+k)--*p;}
 C c;copy(g.begin(),g.end(),c.g.begin());eval(c);return c;
}
void save(const C &c,const string &path){ofstream o(path);o<<"score "<<c.score<<" f "<<c.f<<" q "<<c.q<<"\n";for(int i=0;i<SZ;i++)o<<25+i<<" "<<(c.g[i].op?"or":"and")<<" "<<c.g[i].a<<" "<<c.g[i].b<<"\n";}
int unused_search_main(int argc,char**argv){
 int seconds=argc>1?stoi(argv[1]):1200; if(argc>2)rng.seed(stoull(argv[2]));
 for(int i=0;i<25;i++)for(int j=0;j<N;j++)if(ROWS[j]>>i&1)setbit(val[i],j);
 for(int i : ::fpos)setbit(fp,i);for(int i:fneg)setbit(fn,i);for(int i:qpos)setbit(qp,i);for(int i:qneg)setbit(qn,i);
 auto t0=chrono::steady_clock::now();long long count=0;int best=INT_MAX,restarts=0;C winner;
 while(chrono::duration<double>(chrono::steady_clock::now()-t0).count()<seconds){
  C c=seed();restarts++;int stuck=0;
  for(int it=0;it<100000;it++){
   auto a=active(c);C d=c;int nm=1;while(nm<5&&rnd(4)==0)nm++;
   for(int j=0;j<nm;j++){
    int k=rnd(10)?a[rnd(a.size())]:rnd(SZ);int field=rnd(3);
    if(field==0)d.g[k].op=1-d.g[k].op;
    else if(field==1)d.g[k].a=rnd(25+k);
    else d.g[k].b=rnd(25+k);
   }
   eval(d);count++;
   if(d.score<=c.score){if(d.score<c.score)stuck=0;c=d;}else stuck++;
   if(c.score<best){best=c.score;winner=c;save(c,"/tmp/oec/pequalnp-pilot-37/circuit_search/best.txt");cout<<"best "<<best<<" iterations "<<count<<" restarts "<<restarts<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;}
   if(best==0)return 0;
   if(stuck>20000)break;
   if(count%10000==0&&chrono::duration<double>(chrono::steady_clock::now()-t0).count()>seconds)break;
  }
 }
 cout<<"DONE best "<<best<<" iterations "<<count<<" restarts "<<restarts<<endl;
}

int main(int argc,char**argv) {
 for(int i=0;i<25;i++)for(int j=0;j<N;j++)if(ROWS[j]>>i&1)setbit(val[i],j);
 for(int i : ::fpos)setbit(fp,i);for(int i:fneg)setbit(fn,i);for(int i:qpos)setbit(qp,i);for(int i:qneg)setbit(qn,i);
 C c;string tmp,op;int idx;ifstream in(argv[1]);in>>tmp>>c.score>>tmp>>c.f>>tmp>>c.q;
 for(int i=0;i<SZ;i++){in>>idx>>op>>c.g[i].a>>c.g[i].b;c.g[i].op=(op=="or");}
 eval(c);int base=c.score;long long total=0,neutral=0;
 cout<<"baseline score "<<base<<endl;
 for(int k=0;k<SZ;k++)for(int op=0;op<2;op++)for(int a=0;a<25+k;a++)for(int b=a;b<25+k;b++){
  C d=c;d.g[k]={op,a,b};eval(d);total++;
  if(d.score<=base)neutral++;
  if(d.score<base){cout<<"improved "<<d.score<<" gate "<<25+k<<" op "<<op<<" a "<<a<<" b "<<b<<endl;save(d,"/tmp/oec/pequalnp-pilot-37/circuit_search/exhaust-improved.txt");return 0;}
 }
 cout<<"no improvement over "<<total<<" arbitrary single-gate substitutions; neutral "<<neutral<<endl;
}
