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
constexpr int N=25,K=61,W=13;
using Bits=array<uint64_t,W>;
struct Gate { int a,b,op; };
mt19937_64 rng(132);
vector<uint32_t> pos,neg;
Bits target,positive,taptarget,negative;int tapIndex=N+K-2;
vector<Bits> inputs;
int ones(const Bits&a){int n=0;for(auto x:a)n+=__builtin_popcountll(x);return n;}
Bits fun(const Bits&a,const Bits&b,int op){Bits z;for(int i=0;i<W;i++)z[i]=op?(a[i]|b[i]):(a[i]&b[i]);return z;}
vector<Bits> eval(const vector<Gate>&g){auto w=inputs;for(auto x:g)w.push_back(fun(w[x.a],w[x.b],x.op));return w;}
int score(const Bits&x,int weight=1){int s=0;for(int i=0;i<W;i++){uint64_t e=x[i]^target[i];s+=__builtin_popcountll(e);if(weight>1)s+=(weight-1)*__builtin_popcountll(e&positive[i]);}return s;}
int chooseTap(const vector<Bits>&v){int best=1000000,idx=0,equals=0;for(int i=0;i<(int)v.size();i++){int e=0;for(int q=0;q<W;q++)e+=__builtin_popcountll((v[i][q]^taptarget[q])&negative[q]);if(e<best){best=e;idx=i;equals=1;}else if(e==best&&rng()%++equals==0)idx=i;}return idx;}
int fullscore(const vector<Bits>&v,int weight){tapIndex=chooseTap(v);int s=score(v.back(),weight);for(int q=0;q<W;q++)s+=__builtin_popcountll((v[tapIndex][q]^taptarget[q])&negative[q]);return s;}
int maskedscore(const Bits&a,const Bits&b,int op,const Bits&mask,const Bits&need,int weight){int s=0;for(int i=0;i<W;i++){uint64_t e=((op?(a[i]|b[i]):(a[i]&b[i]))^need[i])&mask[i];s+=__builtin_popcountll(e);if(weight>1)s+=(weight-1)*__builtin_popcountll(e&positive[i]);}return s;}
vector<Gate> seed(){vector<Gate> g;vector<int> centers(12);iota(centers.begin(),centers.end(),0);shuffle(centers.begin(),centers.end(),rng);vector<int> roots;for(int p:centers){vector<int> ls;for(int l=0;l<13;l++)if((p+1+l)%13==0||(p+1+l)%13==1||(p+1+l)%13==3||(p+1+l)%13==9)ls.push_back(12+l);shuffle(ls.begin(),ls.end(),rng);int s=ls[0];for(int i=1;i<(int)ls.size();i++){g.push_back({s,ls[i],1});s=N+g.size()-1;}g.push_back({p,s,0});roots.push_back(N+g.size()-1);}while(roots.size()>2){shuffle(roots.begin(),roots.end(),rng);int a=roots.back();roots.pop_back();int b=roots.back();roots.pop_back();g.push_back({a,b,1});roots.push_back(N+g.size()-1);}vector<int> special={12,13,15,21};shuffle(special.begin(),special.end(),rng);g.push_back({special[0],special[1],1});int a=N+g.size()-1;g.push_back({a,special[2],1});g.push_back({roots[0],roots[1],1});return g;}
void reorder(vector<Gate>&g){
 vector<Gate> out;vector<int> id(N+K,-1);for(int i=0;i<N;i++)id[i]=i;vector<int> todo(K);iota(todo.begin(),todo.end(),0);
 while(!todo.empty()){vector<int> ready;for(int k:todo)if(id[g[k].a]>=0 && id[g[k].b]>=0 && (k<K-1 || todo.size()==1))ready.push_back(k);if(ready.empty()){cerr<<"topo failure"<<endl;exit(2);}int k=ready[rng()%ready.size()];out.push_back({id[g[k].a],id[g[k].b],g[k].op});id[N+k]=N+out.size()-1;todo.erase(find(todo.begin(),todo.end(),k));}g=out;
}
void save(const vector<Gate>&g,string f){ofstream o(f);o<<"{\"inputs\":25,\"f_output\":"<<N+K-1<<",\"tap_output\":"<<tapIndex<<",\"gates\":[";for(int i=0;i<K;i++){if(i)o<<",";o<<"["<<g[i].op<<","<<g[i].a<<","<<g[i].b<<"]";}o<<"]}\n";}
int main(int argc,char**argv){double seconds=argc>1?stod(argv[1]):600;string base=argc>2?argv[2]:".";int weight=argc>3?stoi(argv[3]):4;if(argc>4)rng.seed(stoull(argv[4]));uint32_t all=(1<<13)-1;int adj[12]={};for(int p=0;p<12;p++)for(int l=0;l<13;l++)if((p+1+l)%13==0||(p+1+l)%13==1||(p+1+l)%13==3||(p+1+l)%13==9){adj[p]|=1<<l;pos.push_back((1<<p)|(1<<(12+l)));}for(int s=0;s<(1<<12);s++){int cover=0;for(int p=0;p<12;p++)if(s>>p&1)cover|=adj[p];int t=all^cover,closure=0;for(int p=0;p<12;p++)if(!(adj[p]&t))closure|=1<<p;if(s==closure)neg.push_back(s|(t<<12));}vector<uint32_t> tests=pos;tests.insert(tests.end(),neg.begin(),neg.end());int tapstart=tests.size();for(int l:{0,1,3,9})tests.push_back(1<<(12+l));uint32_t allowed=all^((1<<0)|(1<<1)|(1<<3)|(1<<9));for(int s=0;s<(1<<12);s++){int t=allowed;for(int p=0;p<12;p++)if(s>>p&1)t&=~adj[p];int c=0;for(int p=0;p<12;p++)if(!(adj[p]&t))c|=1<<p;if(c==s)tests.push_back(s|(t<<12));}if(tests.size()>64*W){cerr<<"case overflow"<<endl;return 2;}inputs.resize(N);for(int i=0;i<(int)tests.size();i++){if(i<(int)pos.size()){target[i/64]|=1ull<<(i%64);positive[i/64]|=1ull<<(i%64);}if(i>=tapstart)negative[i/64]|=1ull<<(i%64);if(i>=tapstart&&i<tapstart+4)taptarget[i/64]|=1ull<<(i%64);for(int p=0;p<N;p++)if(tests[i]>>p&1)inputs[p][i/64]|=1ull<<(i%64);}

 auto start=chrono::steady_clock::now();int restarts=0,total=0,best=100000;while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){auto g=seed();reorder(g);auto saved=g;auto vals=eval(g);int current=fullscore(vals,weight),localbest=current,stuck=0;for(int iter=0;iter<3000;iter++){total++;int j=rng()%K;auto low=vals,high=vals;low[N+j].fill(0);high[N+j].fill(~0ull);for(int k=j+1;k<K;k++){low[N+k]=fun(low[g[k].a],low[g[k].b],g[k].op);high[N+k]=fun(high[g[k].a],high[g[k].b],g[k].op);}Bits mask;for(int q=0;q<W;q++)mask[q]=low.back()[q]^high.back()[q];int baseline=score(low.back(),weight);Bits tapmask;for(int q=0;q<W;q++)tapmask[q]=(low[tapIndex][q]^high[tapIndex][q])&negative[q];int oldlocal=maskedscore(vals[g[j].a],vals[g[j].b],g[j].op,mask,target,weight)+maskedscore(vals[g[j].a],vals[g[j].b],g[j].op,tapmask,taptarget,1);int bestlocal=oldlocal;Gate cand=g[j];int equals=1;int n=N+j;
 // Exact best rewrite of one gate on all observed assignments.
 for(int a=0;a<n;a++)for(int b=a;b<n;b++)for(int op=0;op<2;op++){int v=maskedscore(vals[a],vals[b],op,mask,target,weight)+maskedscore(vals[a],vals[b],op,tapmask,taptarget,1);if(v<bestlocal){bestlocal=v;cand={a,b,op};equals=1;}else if(v==bestlocal&&rng()%++equals==0)cand={a,b,op};}
 if(bestlocal<=oldlocal){g[j]=cand;vals=eval(g);current=fullscore(vals,weight);}stuck++;
 if(current<localbest){localbest=current;saved=g;stuck=0;}else if(current==localbest&&rng()%20==0)saved=g;if(current<best){best=current;cout<<"best "<<best<<" unweighted_total "<<fullscore(vals,1)<<" tap "<<tapIndex<<" restart "<<restarts<<" iter "<<total<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;save(g,base+"/best.json");}if(current==0){save(g,base+"/solution.json");return 0;}
 if(stuck>150){g=saved;reorder(g);int count=1+rng()%3;for(int a=0;a<count;a++){int k=rng()%K;int typ=rng()%3;if(typ==0)g[k].op^=1;else if(typ==1)g[k].a=rng()%(N+k);else g[k].b=rng()%(N+k);}vals=eval(g);current=fullscore(vals,weight);stuck=0;}
 if(iter%200==199){reorder(g);vals=eval(g);current=fullscore(vals,weight);} if(iter%30==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
 }restarts++;if(restarts%100==0)cout<<"restart "<<restarts<<" iter "<<total<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;}cout<<"done best="<<best<<" restarts="<<restarts<<" iterations="<<total<<endl;
}
