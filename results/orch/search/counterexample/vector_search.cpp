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
struct Gate{int op,a,b;};using Circuit=array<Gate,11>;
array<uint64_t,17>base{};array<uint64_t,5>target,mask;
mt19937_64 rng;int rnd(int n){return rng()%n;}
void init(){for(int x=0;x<64;x++)for(int i=0;i<6;i++)if(x>>i&1)base[i]|=1ull<<x;
 target[0]=base[1]|base[3]|base[5];target[1]=base[0]|base[1]|base[2];target[2]=base[0]|base[4]|base[5];target[3]=base[3]|base[2]|base[4];target[4]=(base[0]&base[3])|(base[1]&base[4])|(base[2]&base[5]);mask.fill(~0ull);mask[4]=target[3];}
struct Result{int err,penalty;array<int,5>outputs;};
Result score(const Circuit&c){auto w=base;for(int i=0;i<11;i++){auto g=c[i];w[6+i]=g.op==0?w[g.a]&w[g.b]:g.op==1?w[g.a]|w[g.b]:~w[g.a];}
 Result r{};for(int o=0;o<5;o++){int best=100,wire=0;for(int j=0;j<17;j++){int cost=__builtin_popcountll((w[j]^target[o])&mask[o]);if(cost<best){best=cost;wire=j;}}r.err+=best;r.outputs[o]=wire;}
 bool act[17]={};for(int o:r.outputs)act[o]=true;int ns=0;for(int i=10;i>=0;i--)if(act[i+6]){act[c[i].a]=true;if(c[i].op==2)ns++;else act[c[i].b]=true;}r.penalty=ns?0:3;return r;
}
Circuit start(){Circuit c;int t[4][3]={{1,3,5},{0,1,2},{0,4,5},{3,2,4}};for(int i=0;i<4;i++){int k=rnd(3);c[2*i]={1,t[i][k],t[i][(k+1)%3]};c[2*i+1]={1,6+2*i,t[i][(k+2)%3]};}c[8]={0,7,9};c[9]={0,14,11};c[10]={2,rnd(16),0};return c;}
Circuit reorder(Circuit c){Circuit res;bool used[11]={};int map[17];for(int i=0;i<6;i++)map[i]=i;for(int j=0;j<11;j++){vector<int>ready;for(int i=0;i<11;i++)if(!used[i]&&(c[i].a<6||used[c[i].a-6])&&(c[i].op==2||c[i].b<6||used[c[i].b-6]))ready.push_back(i);if(ready.empty())return c;int i=ready[rnd(ready.size())];used[i]=true;map[i+6]=j+6;res[j]={c[i].op,map[c[i].a],c[i].op==2?0:map[c[i].b]};}return res;}
void dump(const Circuit&c,Result r,const string&path){ofstream f(path);for(int i=0;i<11;i++)f<<i+6<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";f<<"outputs";for(int w:r.outputs)f<<" "<<w;f<<"\n";}
int main(int argc,char**argv){int seed=argc>1?stoi(argv[1]):954,seconds=argc>2?stoi(argv[2]):600;string path=argc>3?argv[3]:"vector-best.txt";rng.seed(seed);init();auto t0=chrono::steady_clock::now();long long trials=0,restarts=0;int global=1000;Circuit bestC=start();
 while(chrono::duration<double>(chrono::steady_clock::now()-t0).count()<seconds){Circuit c=(restarts>20&&rnd(2))?reorder(bestC):reorder(start());auto s=score(c);int fit=s.err+s.penalty;for(int k=0;k<200000;k++){
 Circuit d=c;int i=rnd(11),kind=rnd(10);if(kind<2)d[i].op=rnd(3);else if(kind<6)d[i].a=rnd(6+i);else d[i].b=rnd(6+i);if(rnd(20)==0){i=rnd(11);d[i]={rnd(3),rnd(6+i),rnd(6+i)};}int ns=0;for(auto g:d)ns+=g.op==2;if(ns>2)continue;
 auto q=score(d);int nf=q.err+q.penalty;double temp=0.1+3.0*(1.0-double(k%50000)/50000.0);if(nf<=fit||uniform_real_distribution<double>(0,1)(rng)<exp((fit-nf)/temp)){c=d;s=q;fit=nf;}
 if(s.err<global){global=s.err;bestC=c;dump(c,s,path);cout<<"seed="<<seed<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<" trials="<<trials<<" errors="<<s.err<<" penalty="<<s.penalty<<endl;if(!s.err)return 0;}trials++;
 }restarts++;}
 cout<<"DONE trials="<<trials<<" restarts="<<restarts<<" errors="<<global<<endl;
}
