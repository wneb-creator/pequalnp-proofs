#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <bit>
#include <fstream>
#include <cctype>
using namespace std;
struct Gate{int op,a,b;};
using Circuit=vector<Gate>;
Circuit baseline;
using Bits=array<unsigned long long,16>;
array<Bits,10> ins;
Bits target,negative;
vector<pair<int,int>> E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
mt19937_64 rng(109);
int rr(int n){return rng()%n;}
int evaluate(const Circuit& c){
 array<Bits,30>w;
 for(int i=0;i<10;i++) w[i]=ins[i];
 int nt=0;
 for(int g=0;g<(int)c.size();g++){
  auto [op,a,b]=c[g]; nt+=op==2;
  for(int j=0;j<16;j++)w[g+10][j]=op==0?(w[a][j]&w[b][j]):op==1?(w[a][j]|w[b][j]):~w[a][j];
 }
 if(!nt||nt>4)return 10000;
 int err=0;
 for(int j=0;j<16;j++) {auto d=w[c.size()+9][j]^target[j];err+=popcount(d);}
 return err;
}
void show(Circuit c){for(auto g:c)cout<<'['<<g.op<<','<<g.a<<','<<g.b<<"],";cout<<endl;}
Circuit seed(){
 if(!baseline.empty()) return baseline;
 vector<int> inds;
 for(int s=0;s<1024;s++)if(popcount((unsigned)s)==4){bool ok=1;for(auto [i,j]:E)if((s>>i&1)&&(s>>j&1))ok=0;if(ok)inds.push_back(s);}
 int independent=inds[rr(inds.size())];
 vector<vector<int>>N(10);
 for(auto [i,j]:E){if(independent>>i&1)swap(i,j);else if(!(independent>>j&1)&&rr(2))swap(i,j);N[i].push_back(j);}
 vector<int> order;for(int i=0;i<10;i++)if(N[i].size())order.push_back(i);
 shuffle(order.begin(),order.end(),rng);
 Circuit c; vector<int> stars;
 for(int i:order){shuffle(N[i].begin(),N[i].end(),rng);int w=N[i][0];for(int j=1;j<(int)N[i].size();j++){c.push_back({1,w,N[i][j]});w=c.size()+9;}c.push_back({0,i,w});stars.push_back(c.size()+9);}
 shuffle(stars.begin(),stars.end(),rng);int w=stars[0];for(int i=1;i<(int)stars.size();i++){c.push_back({1,w,stars[i]});w=c.size()+9;}
 for(int t=0;t<2;t++){int k=rr(c.size()-1),alias=rr(2)?c[k].a:c[k].b;c.erase(c.begin()+k);for(auto &g:c)for(int*q:{&g.a,&g.b}){if(*q==k+10)*q=alias;else if(*q>k+10)(*q)--;}}
 int k=rr(c.size());for(auto &g:c)for(int*q:{&g.a,&g.b})if(*q>=k+10)(*q)++;
 c.insert(c.begin()+k,{2,rr(10),0});c[k].b=c[k].a;
 return c;
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):600;if(argc>2)rng.seed(atoi(argv[2]));
 if(argc>3){ifstream f(argv[3]);vector<int>v;char ch;int n=-1;while(f.get(ch)){if(isdigit(ch)){if(n<0)n=0;n=n*10+ch-'0';}else if(n>=0){v.push_back(n);n=-1;}}if(v.size()!=57)return 3;for(int i=0;i<57;i+=3)baseline.push_back({v[i],v[i+1],v[i+2]});}
 for(int x=0;x<1024;x++){for(int i=0;i<10;i++)if(x>>i&1)ins[i][x/64]|=1ull<<(x%64);bool f=0;for(auto [i,j]:E)if((x>>i&1)&&(x>>j&1))f=1;(f?target:negative)[x/64]|=1ull<<(x%64);}
 auto started=chrono::steady_clock::now();long long tries=0;int best=10000;
 while(chrono::duration<double>(chrono::steady_clock::now()-started).count()<seconds){
  Circuit c=seed();int score=evaluate(c);
  for(int t=0;t<50000;t++){
   Circuit old=c;
   if(rr(10)==0){
    int k=rr(17);if(c[k+1].a!=k+10&&c[k+1].b!=k+10){swap(c[k],c[k+1]);for(int j=k+2;j<19;j++)for(int*p:{&c[j].a,&c[j].b}){if(*p==k+10)*p=k+11;else if(*p==k+11)*p=k+10;}}
   }else{
    int nm=rr(100)<15?(rr(3)==0?3:2):1;
    for(int z=0;z<nm;z++){int k=rr(c.size()),field=rr(10);if(field<2)c[k].op=rr(3);else if(field<6)c[k].a=rr(k+10);else c[k].b=rr(k+10);if(c[k].op==2)c[k].b=c[k].a;}
   }
   int ns=evaluate(c);tries++;double temp=0.02+0.8*(50000-t)/50000.;
   if(ns<=score||generate_canonical<double,53>(rng)<exp((score-ns)/temp))score=ns;else c=old;
   if(score<best){best=score;cout<<"best "<<best<<" trials "<<tries<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;show(c);}
   if(score==0){cout<<"WITNESS"<<endl;return 0;}
  }
 }
 cout<<"finished best "<<best<<" trials "<<tries<<endl;
}
