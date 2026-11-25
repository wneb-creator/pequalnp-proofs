#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
using U=uint64_t;
struct Gate{int op,a,b;};
struct Circuit{std::array<Gate,64>g;int bypass;};
int n,k,rows;U target;std::array<U,64>ins;
U rngstate;
U rnd(){rngstate^=rngstate<<13;rngstate^=rngstate>>7;rngstate^=rngstate<<17;return rngstate;}
int score(const Circuit&c){std::array<U,128>w;std::array<int,128>col;for(int i=0;i<n;i++){w[i]=ins[i];col[i]=i<7?1:2;}for(int j=0;j<k;j++){auto g=c.g[j];int m=n+j;if(j==c.bypass){w[m]=w[g.a];col[m]=col[g.a];}else if(g.op){w[m]=w[g.a]|w[g.b];col[m]=col[g.a]|col[g.b];if(col[m]==3)return 999;}else{w[m]=w[g.a]&w[g.b];col[m]=0;}}return std::popcount(w[n+k-1]^target);}
void show(const Circuit&c,int s,U iterations,double secs){std::cout<<"BEST score="<<s<<" iterations="<<iterations<<" seconds="<<secs<<" bypass="<<c.bypass<<std::endl;for(int j=0;j<k;j++)std::cout<<j<<" "<<c.g[j].op<<" "<<c.g[j].a<<" "<<c.g[j].b<<"\n";std::cout.flush();}
int main(int argc,char**argv){std::ifstream f(argv[1]);f>>n>>k>>rows>>target;for(int i=0;i<n;i++)f>>ins[i];Circuit base;for(int j=0;j<k;j++)f>>base.g[j].op>>base.g[j].a>>base.g[j].b;rngstate=std::strtoull(argv[3],nullptr,10);double limit=std::atof(argv[2]);auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};Circuit best=base;int bs=999;U iter=0,restarts=0;
 while(elapsed()<limit){Circuit c=base;c.bypass=rnd()%k;if(rnd()%2)c.g[c.bypass].a=c.g[c.bypass].b;int cs=score(c);if(cs==999)continue;restarts++;
  for(int step=0;step<40000;step++){iter++;Circuit next=c;int j=rnd()%k;int which=rnd()%24;if(which==0)next.bypass=rnd()%k;else if(which==1)next.g[j].op^=1;else if((which&1)||j==next.bypass)next.g[j].a=rnd()%(n+j);else next.g[j].b=rnd()%(n+j);int ns=score(next);double temp=0.04+0.56*(1.0-double(step)/40000);bool accept=ns<=cs||(ns<999&&double(rnd()>>11)*(1.0/9007199254740992.0)<std::exp(double(cs-ns)/temp));if(accept){c=next;cs=ns;}if(cs<bs){best=c;bs=cs;show(best,bs,iter,elapsed());if(bs==0){std::cout<<"FOUND exact boundary circuit"<<std::endl;return 42;}}
   if((iter&1048575)==0&&elapsed()>=limit)break;
  }
 }
 std::cout<<"DONE iterations="<<iter<<" restarts="<<restarts<<" best="<<bs<<" seconds="<<elapsed()<<std::endl;
}
