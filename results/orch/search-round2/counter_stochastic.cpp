#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
int n,rows,positive,k0,k;vector<array<int,3>> original,cur,bestc;
vector<uint64_t> inputs;uint64_t target;mt19937_64 rng(1031);
uint64_t calls=0;
int score(const vector<array<int,3>>&g) {uint64_t w[128];copy(inputs.begin(),inputs.end(),w);for(int j=0;j<k;j++){auto[op,a,b]=g[j];w[n+j]=op?(w[a]|w[b]):(w[a]&w[b]);}calls++;return __builtin_popcountll(w[n+k-1]^target);}
vector<array<int,3>> drop(int q,int substitute) {auto g=original;int replacement=g[q][substitute];g.erase(g.begin()+q);for(auto &h:g)for(int r=1;r<3;r++){if(h[r]==n+q)h[r]=replacement;else if(h[r]>n+q)h[r]--;}return g;}
void show(const vector<array<int,3>>&g) {for(int j=0;j<k;j++)cout<<j<<" "<<g[j][0]<<" "<<g[j][1]<<" "<<g[j][2]<<"\n";cout.flush();}
int main(int argc,char**argv) {if(argc<3)return 2;ifstream f(argv[1]);int seconds=atoi(argv[2]);f>>n>>rows>>positive>>k0;k=k0-1;
 vector<int>assign(rows);for(int&i:assign)f>>i;
 for(int i=0;i<n;i++){uint64_t tt=0;for(int j=0;j<rows;j++)if(assign[j]>>i&1)tt|=1ull<<j;inputs.push_back(tt);}
 target=(1ull<<positive)-1;original.resize(k0);for(auto&g:original)f>>g[0]>>g[1]>>g[2];
 int best=999,restarts=0;auto start=chrono::steady_clock::now();
 cout<<"n="<<n<<" rows="<<rows<<" positive="<<positive<<" k="<<k<<" seconds="<<seconds<<"\n";
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  restarts++;cur=drop(rng()%k0,1+rng()%2);int sc=score(cur);
  if(restarts%4==0&&!bestc.empty()){cur=bestc;sc=best;}
  for(int it=0;it<50000;it++){
   int j=rng()%k,which=rng()%3;auto old=cur[j];
   if(which==0)cur[j][0]^=1;else {cur[j][which]=rng()%(n+j);if(cur[j][1]==cur[j][2]){cur[j]=old;continue;}}
   int ns=score(cur);double phase=double(it)/50000;double temp=2.5*(1-phase)*(1-phase)+0.03;
   bool accept=ns<=sc||generate_canonical<double,53>(rng)<exp(double(sc-ns)/temp);
   if(accept)sc=ns;else cur[j]=old;
   if(sc<best){best=sc;bestc=cur;cout<<"best="<<best<<" calls="<<calls<<" restart="<<restarts<<" elapsed="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";show(bestc);}
   if(best==0){cout<<"FOUND\n";return 0;}
  }
 }
 cout<<"FINISHED best="<<best<<" calls="<<calls<<" restarts="<<restarts<<"\n";show(bestc);
}
