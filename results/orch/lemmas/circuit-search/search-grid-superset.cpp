#include <array>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
constexpr int N=17,K=28,W=2,L=6,R=11;int adj[L];
using Bits=array<uint64_t,W>;
struct Gate { int a,b,op; };
mt19937_64 rng(132);
vector<uint32_t> pos,neg;
Bits target,positive;array<Bits,8> costplanes;vector<int> costs;bool positivePriority=true;
vector<Bits> inputs;
int ones(const Bits&a){int n=0;for(auto x:a)n+=__builtin_popcountll(x);return n;}
Bits fun(const Bits&a,const Bits&b,int op){Bits z;for(int i=0;i<W;i++)z[i]=op?(a[i]|b[i]):(a[i]&b[i]);return z;}
vector<Bits> eval(const vector<Gate>&g){auto w=inputs;for(auto x:g)w.push_back(fun(w[x.a],w[x.b],x.op));return w;}
void resetCosts(){costs.assign(pos.size()+neg.size(),1);for(auto &p:costplanes)p.fill(0);for(int i=0;i<(int)costs.size();i++)costplanes[0][i/64]|=1ull<<(i%64);}
void punish(const Bits&v){for(int i=0;i<(int)costs.size();i++)if((v[i/64]^target[i/64])>>(i%64)&1)costs[i]=min(255,costs[i]+1);for(auto &p:costplanes)p.fill(0);for(int i=0;i<(int)costs.size();i++)for(int q=0;q<8;q++)if(costs[i]>>q&1)costplanes[q][i/64]|=1ull<<(i%64);}
int rawscore(const Bits&x){int s=0;for(int i=0;i<W;i++)s+=__builtin_popcountll(x[i]^target[i]);return s;}
int score(const Bits&x,int weight=1){int s=0;for(int i=0;i<W;i++){uint64_t e=x[i]^target[i];for(int q=0;q<8;q++)s+=(1<<q)*__builtin_popcountll(e&costplanes[q][i]);if(positivePriority)s+=262144*__builtin_popcountll(e&positive[i]);}return s;}
int maskedscore(const Bits&a,const Bits&b,int op,const Bits&mask,const Bits&need,int weight){int s=0;for(int i=0;i<W;i++){uint64_t e=((op?(a[i]|b[i]):(a[i]&b[i]))^need[i])&mask[i];if(e)for(int q=0;q<8;q++)s+=(1<<q)*__builtin_popcountll(e&costplanes[q][i]);if(positivePriority)s+=262144*__builtin_popcountll(e&positive[i]);}return s;}
int properDirty(const vector<Gate>&g){auto sig=eval(g);array<bool,N+K>active={};vector<int>todo={N+K-1};while(!todo.empty()){int a=todo.back();todo.pop_back();if(active[a])continue;active[a]=true;if(a>=N){todo.push_back(g[a-N].a);todo.push_back(g[a-N].b);}}array<bool,K>bad={};for(int a=0;a<N;a++)for(int b=a;b<N;b++){bool edge=a<L&&b>=L&&(adj[a]>>(b-L)&1);if(edge)continue;array<bool,N+K>v={};v[a]=v[b]=true;for(int j=0;j<K;j++){v[N+j]=g[j].op?(v[g[j].a]||v[g[j].b]):(v[g[j].a]&&v[g[j].b]);if(active[N+j]&&!g[j].op&&v[N+j])bad[j]=true;}}for(int j=0;j<K;j++)if(bad[j])for(int a=0;a<N+j;a++)if(sig[N+j]==sig[a]){bad[j]=false;break;}return count(bad.begin(),bad.end(),true);}
vector<Gate> seed(){vector<Gate> g;vector<int> centers(L);iota(centers.begin(),centers.end(),0);shuffle(centers.begin(),centers.end(),rng);vector<int> roots;for(int p:centers){vector<int> ns;for(int l=0;l<R;l++)if(adj[p]>>l&1)ns.push_back(L+l);shuffle(ns.begin(),ns.end(),rng);int z=ns[0];for(int i=1;i<(int)ns.size();i++){g.push_back({z,ns[i],1});z=N+g.size()-1;}g.push_back({p,z,0});roots.push_back(N+g.size()-1);}while(roots.size()>1){shuffle(roots.begin(),roots.end(),rng);int a=roots.back();roots.pop_back();int b=roots.back();roots.pop_back();g.push_back({a,b,1});roots.push_back(N+g.size()-1);}vector<int> choices;for(int j=0;j<(int)g.size();j++)if(g[j].op==0)choices.push_back(j);int removed=choices[rng()%choices.size()];int replacement=rng()%2?g[removed].a:g[removed].b;auto map=[&](int i){if(i==N+removed)return replacement;return i>N+removed?i-1:i;};vector<Gate> ng;for(int j=0;j<(int)g.size();j++)if(j!=removed)ng.push_back({map(g[j].a),map(g[j].b),g[j].op});return ng;}
void reorder(vector<Gate>&g){
 vector<Gate> out;vector<int> id(N+K,-1);for(int i=0;i<N;i++)id[i]=i;vector<int> todo(K);iota(todo.begin(),todo.end(),0);
 while(!todo.empty()){vector<int> ready;for(int k:todo)if(id[g[k].a]>=0 && id[g[k].b]>=0 && (k<K-1 || todo.size()==1))ready.push_back(k);if(ready.empty()){cerr<<"topo failure"<<endl;exit(2);}int k=ready[rng()%ready.size()];out.push_back({id[g[k].a],id[g[k].b],g[k].op});id[N+k]=N+out.size()-1;todo.erase(find(todo.begin(),todo.end(),k));}g=out;
}
void save(const vector<Gate>&g,string f){ofstream o(f);o<<"[";for(int i=0;i<K;i++){if(i)o<<",";o<<"["<<g[i].op<<","<<g[i].a<<","<<g[i].b<<"]";}o<<"]\n";}
int main(int argc,char**argv){if(argc<6){cerr<<"missing arguments"<<endl;return 2;}double seconds=argc>1?stod(argv[1]):600;string base=argc>2?argv[2]:".";int weight=argc>3?stoi(argv[3]):4;if(argc>4)rng.seed(stoull(argv[4]));ifstream af(argv[5]);for(int&a:adj)if(!(af>>a)||a<=0||(a>>R)!=0){cerr<<"invalid adjacency file"<<endl;return 2;}uint32_t all=(1<<R)-1;for(int p=0;p<L;p++)for(int l=0;l<R;l++)if(adj[p]>>l&1)pos.push_back((1<<p)|(1<<(L+l)));for(int ss=0;ss<(1<<L);ss++){int cover=0;for(int p=0;p<L;p++)if(ss>>p&1)cover|=adj[p];int tt=all^cover,c=0;for(int p=0;p<L;p++)if(!(adj[p]&tt))c|=1<<p;if(c==ss)neg.push_back(ss|(tt<<L));}vector<uint32_t> tests=pos;tests.insert(tests.end(),neg.begin(),neg.end());if(tests.size()>W*64){cerr<<"case overflow"<<endl;return 2;}inputs.resize(N);for(int i=0;i<(int)tests.size();i++){if(i<(int)pos.size()){target[i/64]|=1ull<<(i%64);positive[i/64]|=1ull<<(i%64);}for(int p=0;p<N;p++)if(tests[i]>>p&1)inputs[p][i/64]|=1ull<<(i%64);}

 auto start=chrono::steady_clock::now();int total=0,restarts=0,best=1000,bestDirty=1000,bestSuper=1000;vector<int> errorSeen(pos.size()+neg.size());
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){auto g=seed();reorder(g);auto vals=eval(g);resetCosts();positivePriority=true;
 for(int iter=0;iter<30000;iter++){total++;int j=rng()%K;auto low=vals,high=vals;low[N+j].fill(0);high[N+j].fill(~0ull);for(int k=j+1;k<K;k++){low[N+k]=fun(low[g[k].a],low[g[k].b],g[k].op);high[N+k]=fun(high[g[k].a],high[g[k].b],g[k].op);}Bits mask;for(int q=0;q<W;q++)mask[q]=low.back()[q]^high.back()[q];int oldlocal=maskedscore(vals[g[j].a],vals[g[j].b],g[j].op,mask,target,1);int bestlocal=oldlocal;Gate cand=g[j];int equals=1;
 for(int a=0;a<N+j;a++)for(int b=a;b<N+j;b++)for(int op=0;op<2;op++){int v=maskedscore(vals[a],vals[b],op,mask,target,1);if(v<bestlocal){bestlocal=v;cand={a,b,op};equals=1;}else if(v==bestlocal&&rng()%++equals==0)cand={a,b,op};}g[j]=cand;vals=eval(g);int raw=rawscore(vals.back());if((vals.back()[0]^target[0])&positive[0]){cerr<<"positive invariant failed"<<endl;return 2;}if(raw<best){best=raw;cout<<"best raw="<<best<<" iter="<<total<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;save(g,base+"/best.json");}if(raw==0){save(g,base+"/solution.json");return 0;}
 if(iter%100==99){punish(vals.back());for(int i=0;i<(int)errorSeen.size();i++)if((vals.back()[i/64]^target[i/64])>>(i%64)&1)errorSeen[i]++;}
 if(iter%1000==999){int dc=properDirty(g);int fn=__builtin_popcountll((vals.back()[0]^target[0])&positive[0]);if(fn==0&&raw<bestSuper){bestSuper=raw;cout<<"superset falsepositives="<<raw<<" dirty="<<dc<<" iter="<<total<<endl;save(g,base+"/best-super.json");}if(dc&&raw<bestDirty){bestDirty=raw;cout<<"proper dirty candidate raw="<<raw<<" count="<<dc<<" iter="<<total<<endl;save(g,base+"/best-dirty.json");}reorder(g);vals=eval(g);}
 if(iter%1500==1499 && iter+1<30000){auto oldg=g;auto oldvals=vals;for(int z=0;z<2;z++){int k=rng()%K;if(rng()%2)g[k].a=rng()%(N+k);else g[k].b=rng()%(N+k);}vals=eval(g);if((vals.back()[0]^target[0])&positive[0]){g=oldg;vals=oldvals;}}
 if(iter%30==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
 }if(rawscore(vals.back())==0){save(g,base+"/solution.json");return 0;}restarts++;cout<<"restart="<<restarts<<" iterations="<<total<<" positivePriority="<<positivePriority<<" weighted="<<score(vals.back())<<" raw="<<rawscore(vals.back())<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;}
 int ep=0,en=0;for(int i=0;i<(int)errorSeen.size();i++)if(errorSeen[i]){if(i<(int)pos.size())ep++;else en++;}cout<<"done best="<<best<<" bestProperDirty="<<bestDirty<<" sampledPositiveErrors="<<ep<<" sampledNegativeErrors="<<en<<" iterations="<<total<<endl;ofstream counts(base+"/error-counts.json");counts<<"[";for(int i=0;i<(int)errorSeen.size();i++){if(i)counts<<",";counts<<errorSeen[i];}counts<<"]\n";
}
