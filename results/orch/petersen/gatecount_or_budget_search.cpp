#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using U=uint64_t;
struct Node{U a,b;};
struct Circuit{std::vector<Node> g; U out;};
std::mt19937_64 rng(2583);
U bit(int i){return U(1)<<i;}
U conj(U mask,const std::vector<U>&v,U full){ U f=full; while(mask){int i=__builtin_ctzll(mask);f&=v[i];mask&=mask-1;}return f;}
U evaluate(const Circuit&C,const std::vector<U>&x,U full){auto v=x;for(auto g:C.g)v.push_back(conj(g.a,v,full)|conj(g.b,v,full));return conj(C.out,v,full);}
Circuit removeGate(const Circuit&C,int n,int j,bool branch){Circuit D=C;U r=branch?C.g[j].b:C.g[j].a;int del=n+j;auto remap=[&](U mask){if(mask&bit(del)){mask^=bit(del);mask|=r;}return (mask&(bit(del)-1))|((mask>>(del+1))<<del);};D.g.erase(D.g.begin()+j);for(int i=j;i<(int)D.g.size();i++){D.g[i].a=remap(D.g[i].a);D.g[i].b=remap(D.g[i].b);}D.out=remap(D.out);return D;}
void print(const Circuit&C,int n){for(int j=0;j<(int)C.g.size();j++)std::cout<<"g "<<n+j<<" "<<C.g[j].a<<" "<<C.g[j].b<<"\n";std::cout<<"out "<<C.out<<"\n";}
int andCost(const Circuit&C){int c=std::max(0,__builtin_popcountll(C.out)-1);for(auto g:C.g)c+=std::max(0,__builtin_popcountll(g.a)-1)+std::max(0,__builtin_popcountll(g.b)-1);return c;}
int main(int argc,char**argv){if(argc<3)return 2;int seconds=std::stoi(argv[2]);int budget=std::stoi(argv[3]);std::ifstream in(argv[1]);int n,k,a;U want;in>>n>>k>>a>>want;U full=a==64?~U(0):(bit(a)-1);std::vector<U>x(n);for(auto&z:x)in>>z;Circuit base;base.g.resize(k);for(auto&g:base.g)in>>g.a>>g.b;in>>base.out;std::vector<Circuit>seeds{base};
double global=1000000;Circuit best;unsigned long long iter=0,restarts=0;auto start=std::chrono::steady_clock::now();while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds){Circuit C=seeds[rng()%seeds.size()];double score=__builtin_popcountll(evaluate(C,x,full)^want)+0.08*std::max(0,andCost(C)-budget);double temp=0.15+0.4*(double(rng()%1000)/1000);for(int step=0;step<100000;step++,iter++){Circuit D=C;int which=rng()%(2*k+1);U *p;int avail;if(which==2*k){p=&D.out;avail=n+k;}else{int g=which/2;p=which%2?&D.g[g].b:&D.g[g].a;avail=n+g;}int mode=rng()%100;if(mode<85){*p^=bit(rng()%avail);}else if(mode<95){*p=bit(rng()%avail);}else{*p=rng()&(bit(avail)-1);if(rng()%2)*p&=rng();}if(!*p)*p=bit(rng()%avail);int err=__builtin_popcountll(evaluate(D,x,full)^want);int cost=andCost(D);double ns=err+0.08*std::max(0,cost-budget);if(ns<global){global=ns;best=D;std::cout<<"best "<<global<<" errors "<<err<<" AND "<<cost<<" iter "<<iter<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";print(best,n);std::cout.flush();}if(err==0 && cost<=budget)return 0;if(ns<=score || double(rng()%1000000)/1000000<std::exp(double(score-ns)/temp)){C=D;score=ns;}if(step%10000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=seconds)break;}restarts++;}std::cout<<"done best "<<global<<" iterations "<<iter<<" restarts "<<restarts<<"\n";return 1;}
