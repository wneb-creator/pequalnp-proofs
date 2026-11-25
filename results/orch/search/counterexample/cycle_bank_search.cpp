#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <fstream>
#include <iostream>
#include <cmath>
using namespace std;struct Gate{int op,a,b;};using Circuit=array<Gate,7>;array<unsigned long long,16>base{};unsigned long long target=0;mt19937_64 rng(961);int rnd(int n){return rng()%n;}int op(){const int a[]={0,1,2,4};return a[rnd(4)];}
void init(){for(int x=0;x<64;x++){for(int i=0;i<6;i++)if(x>>i&1)base[i]|=1ull<<x;bool b=false;for(int i=0;i<6;i++)b|=(x>>i&1)&&(x>>((i+1)%6)&1);if(b)target|=1ull<<x;}for(int i=0;i<3;i++)base[i+6]=base[i]|base[i+3];}
int score(const Circuit&c){auto w=base;for(int i=0;i<7;i++){auto g=c[i];w[i+9]=g.op==1?w[g.a]|w[g.b]:g.op==0?w[g.a]&w[g.b]:g.op==2?~w[g.a]&w[g.b]:w[g.a]&~w[g.b];}return __builtin_popcountll(w[15]^target);}
Circuit start(){vector<Gate>v;vector<int>ts;for(int i:{0,2,4}){v.push_back({1,(i+1)%6,(i+5)%6});v.push_back({0,i,8+(int)v.size()});ts.push_back(8+v.size());}v.push_back({1,ts[0],ts[1]});v.push_back({1,8+(int)v.size(),ts[2]});int drop=rnd(7),rep=rnd(2)?v[drop].a:v[drop].b;v.erase(v.begin()+drop);for(auto&g:v)for(int*p:{&g.a,&g.b}){if(*p==9+drop)*p=rep;else if(*p>9+drop)--*p;}Circuit c;copy(v.begin(),v.end(),c.begin());return c;}
void dump(const Circuit&c){ofstream f("/tmp/oec/pequalnp-pilot-95/counterexample/cycle-bank-best.txt");for(int i=0;i<7;i++)f<<i+9<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";}
int main(int argc,char**argv){init();int secs=argc>1?stoi(argv[1]):30,global=1000;long long trials=0;auto t=chrono::steady_clock::now();while(chrono::duration<double>(chrono::steady_clock::now()-t).count()<secs){Circuit c=start();int f=score(c);for(int k=0;k<100000;k++){Circuit d=c;int i=rnd(7),z=rnd(3);if(z==0)d[i].op=op();else if(z==1)d[i].a=rnd(9+i);else d[i].b=rnd(9+i);if(rnd(20)==0){i=rnd(7);d[i]={op(),rnd(9+i),rnd(9+i)};}int g=score(d);double temp=.1+1.5*(1.-double(k%25000)/25000.);if(g<=f||uniform_real_distribution<double>(0,1)(rng)<exp((f-g)/temp)){c=d;f=g;}if(f<global){global=f;dump(c);cout<<"errors="<<f<<" trials="<<trials<<endl;if(!f)return 0;}trials++;}}cout<<"DONE errors="<<global<<" trials="<<trials<<endl;}
