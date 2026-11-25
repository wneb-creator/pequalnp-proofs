#include <array>
#include <vector>
#include <random>
#include <iostream>
#include <fstream>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdint>
using namespace std;
struct TT{uint64_t lo=0,hi=0;};
TT operator&(TT a,TT b){return{a.lo&b.lo,a.hi&b.hi};}TT operator|(TT a,TT b){return{a.lo|b.lo,a.hi|b.hi};}TT operator^(TT a,TT b){return{a.lo^b.lo,a.hi^b.hi};}TT operator~(TT a){return{~a.lo,~a.hi};}
int pop(TT a){return __builtin_popcountll(a.lo)+__builtin_popcountll(a.hi);}
struct Gate{int op,a,b;};using Circuit=array<Gate,13>;
array<TT,20>base{};array<TT,4>target,mask;
mt19937_64 rng;int rnd(int n){return rng()%n;}
void init(){for(int x=0;x<128;x++)for(int i=0;i<7;i++)if(x>>i&1){if(x<64)base[i].lo|=1ull<<x;else base[i].hi|=1ull<<(x-64);}
 target[0]=base[6]|base[0]|base[3];target[1]=base[6]|base[1]|base[4];target[2]=base[6]|base[2]|base[5];target[3]={};for(int i=0;i<6;i++)target[3]=target[3]|(base[i]&base[(i+1)%6]);mask.fill({~0ull,~0ull});}
struct Result{int err,penalty;array<int,4>outputs;};
Result score(const Circuit&c){auto w=base;for(int i=0;i<13;i++){auto g=c[i];w[7+i]=g.op==0?w[g.a]&w[g.b]:g.op==1?w[g.a]|w[g.b]:~w[g.a];}
 Result r{};for(int o=0;o<4;o++){int best=1000,wire=0;for(int j=0;j<20;j++){int cost=pop((w[j]^target[o])&mask[o]);if(cost<best){best=cost;wire=j;}}r.err+=best;r.outputs[o]=wire;}
 bool act[20]={};for(int o:r.outputs)act[o]=true;int ns=0;for(int i=12;i>=0;i--)if(act[i+7]){act[c[i].a]=true;if(c[i].op==2)ns++;else act[c[i].b]=true;}bool bank[20]={};for(int k=0;k<3;k++)bank[r.outputs[k]]=true;bool complex=false;for(int i=12;i>=0;i--)if(bank[i+7]){complex|=c[i].op!=1;bank[c[i].a]=true;if(c[i].op!=2)bank[c[i].b]=true;}r.penalty=(ns?0:4)+(complex?0:4);return r;
}
Circuit start(){vector<Gate>v;for(int i=0;i<3;i++){int t[3]={6,i,i+3};int k=rnd(3);v.push_back({1,t[k],t[(k+1)%3]});v.push_back({1,7+2*i,t[(k+2)%3]});}
 vector<int> terms;for(int i:{0,2,4}){v.push_back({1,(i+1)%6,(i+5)%6});int z=6+v.size();v.push_back({0,i,z});terms.push_back(6+v.size());}v.push_back({1,terms[0],terms[1]});v.push_back({1,6+int(v.size()),terms[2]});
 int drop=rnd(14),rep=rnd(2)?v[drop].a:v[drop].b;v.erase(v.begin()+drop);for(auto&g:v)for(int*q:{&g.a,&g.b}){if(*q==7+drop)*q=rep;else if(*q>7+drop)--*q;}Circuit c;copy(v.begin(),v.end(),c.begin());return c;}
Circuit reorder(Circuit c){Circuit res;bool used[13]={};int map[20];for(int i=0;i<7;i++)map[i]=i;for(int j=0;j<13;j++){vector<int>ready;for(int i=0;i<13;i++)if(!used[i]&&(c[i].a<7||used[c[i].a-7])&&(c[i].op==2||c[i].b<7||used[c[i].b-7]))ready.push_back(i);if(ready.empty())return c;int i=ready[rnd(ready.size())];used[i]=true;map[i+7]=j+7;res[j]={c[i].op,map[c[i].a],c[i].op==2?0:map[c[i].b]};}return res;}
void dump(const Circuit&c,Result r,const string&path){ofstream f(path);for(int i=0;i<13;i++)f<<i+7<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";f<<"outputs";for(int w:r.outputs)f<<" "<<w;f<<"\n";}
int main(int argc,char**argv){int seed=argc>1?stoi(argv[1]):954,seconds=argc>2?stoi(argv[2]):1200;string path=argc>3?argv[3]:"vector-best.txt";rng.seed(seed);init();auto t0=chrono::steady_clock::now();long long trials=0,restarts=0;int global=1000,globalPenalty=1000,globalActive=1000;Circuit bestC=start();if(argc>4){ifstream f(argv[4]);int wire;Circuit warm;bool ok=true;for(auto&g:warm)if(!(f>>wire>>g.op>>g.a>>g.b))ok=false;if(ok){bestC=warm;auto q=score(warm);global=q.err;globalPenalty=q.penalty;restarts=21;dump(warm,q,path);cout<<"WARM errors="<<global<<" penalty="<<globalPenalty<<endl;}}
 while(chrono::duration<double>(chrono::steady_clock::now()-t0).count()<seconds){Circuit c=(restarts>20&&rnd(2))?reorder(bestC):reorder(start());auto s=score(c);int fit=s.err+s.penalty;for(int k=0;k<200000;k++){
 Circuit d=c;int i=rnd(13),kind=rnd(10);if(kind<2)d[i].op=rnd(3);else if(kind<6)d[i].a=rnd(7+i);else d[i].b=rnd(7+i);if(rnd(20)==0){i=rnd(13);d[i]={rnd(3),rnd(7+i),rnd(7+i)};}for(auto&g:d)if(g.op==2){g.a=6;g.b=0;}int ns=0;for(auto g:d)ns+=g.op==2;if(ns>1)continue;
 auto q=score(d);int nf=q.err+q.penalty;double temp=0.1+3.0*(1.0-double(k%50000)/50000.0);if(nf<=fit||uniform_real_distribution<double>(0,1)(rng)<exp((fit-nf)/temp)){c=d;s=q;fit=nf;}
 if(s.err<global||(s.err==global&&s.penalty<globalPenalty)){global=s.err;globalPenalty=s.penalty;bestC=c;dump(c,s,path);cout<<"seed="<<seed<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<" trials="<<trials<<" errors="<<s.err<<" penalty="<<s.penalty<<endl;if(!s.err)return 0;}if(s.penalty==0&&s.err<globalActive){globalActive=s.err;dump(c,s,path+".active.txt");cout<<"ACTIVE errors="<<s.err<<" trials="<<trials<<endl;}trials++;
 }restarts++;if(restarts%100==0)cout<<"PROGRESS trials="<<trials<<" restarts="<<restarts<<" best="<<global<<endl;}
 cout<<"DONE trials="<<trials<<" restarts="<<restarts<<" errors="<<global<<endl;
}
