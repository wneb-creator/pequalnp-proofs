#include <iostream>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
using U=__uint128_t;
uint64_t seed=0x9e3779b97f4a7c15ull;
uint64_t rng(){seed^=seed<<7;seed^=seed>>9;return seed;}
int ri(int n){return rng()%n;}
struct Gate{int op,a,b;};
using Circ=std::array<Gate,13>;
U vars[7],target;long long evals=0;
int eval(const Circ& c){U w[20];for(int i=0;i<7;i++)w[i]=vars[i];for(int i=0;i<13;i++){auto g=c[i];w[7+i]=g.op==0?(w[g.a]&w[g.b]):g.op==1?(w[g.a]|w[g.b]):~w[g.a];}U d=w[19]^target;evals++;return __builtin_popcountll((uint64_t)d)+__builtin_popcountll((uint64_t)(d>>64));}
void show(const Circ& c){for(int i=0;i<13;i++){auto g=c[i];std::cout<<i+7<<":"<<(g.op==0?"AND":g.op==1?"OR":"NOT")<<"("<<g.a<<","<<g.b<<") ";}std::cout<<std::endl;}
Circ randomcirc(){Circ c;int ng=ri(20);for(int i=0;i<13;i++)c[i]={i==ng?2:ri(2),ri(7+i),ri(7+i)};return c;}
Circ shorten(int k,int pick){Gate full[14]={{0,0,2},{0,1,4},{1,0,3},{0,5,9},{1,0,2},{1,4,6},{0,11,12},{1,3,5},{1,1,6},{0,14,15},{1,7,8},{1,10,13},{1,17,18},{1,19,16}};Circ c;int repl=pick?full[k].b:full[k].a;int j=0;for(int i=0;i<14;i++)if(i!=k){auto g=full[i];int *p[2]={&g.a,&g.b};for(auto q:p){if(*q==7+k)*q=repl;if(*q>7+k)(*q)--;}c[j++]=g;}return c;}
int main(int argc,char**argv){int sec=argc>1?std::stoi(argv[1]):300;if(argc>2)seed=std::stoull(argv[2]);
 for(int i=0;i<7;i++){vars[i]=0;for(int x=0;x<128;x++)if(x>>i&1)vars[i]|=U(1)<<x;}
 int E[12][2]={{0,2},{1,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{2,6},{3,6},{5,6}};target=0;for(auto e:E)target|=vars[e[0]]&vars[e[1]];
 auto start=std::chrono::steady_clock::now();int best=128;Circ winner{};long long runs=0;
 while(true){double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(elapsed>sec)break;runs++;
  Circ c=runs%3==0?randomcirc():runs%3==1?shorten(ri(13),ri(2)):winner;if(best==128)c=randomcirc();
  int cur=eval(c);double temp=.2+(ri(5))*.25;
  for(int step=0;step<20000;step++){
   Circ d=c;int i=ri(13),kind=ri(10);if(kind<4){if(ri(2))d[i].a=ri(7+i);else d[i].b=ri(7+i);}else if(kind<7){d[i]={ri(2),ri(7+i),ri(7+i)};}else if(kind<9)d[i].op=1-(d[i].op%2);else{for(auto&g:d)if(g.op==2)g.op=ri(2);d[i].op=ri(3);}
   int score=eval(d);if(score<best){best=score;winner=d;std::cout<<"BEST "<<best<<" evals "<<evals<<" seconds "<<elapsed<<std::endl;show(d);if(best==0)return 0;}
   if(score<=cur||(rng()%1000000)<1000000*std::exp((cur-score)/temp)){c=d;cur=score;}
   if(step%2000==1999&&ri(3)==0){temp=.2+(ri(5))*.25;}
  }
 }
 std::cout<<"FINAL best "<<best<<" evals "<<evals<<" runs "<<runs<<std::endl;show(winner);
}
