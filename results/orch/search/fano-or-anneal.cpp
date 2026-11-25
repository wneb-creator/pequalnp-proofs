#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
using U=uint64_t;
struct Circuit{std::array<U,64>a,b;U out;int bypass;};
int n,k,rows;U target,ones;std::array<U,64>ins;U rngstate;
U rnd(){rngstate^=rngstate<<13;rngstate^=rngstate>>7;rngstate^=rngstate<<17;return rngstate;}
U product(U mask,const std::array<U,128>&w){U v=ones;while(mask){int i=std::countr_zero(mask);mask&=mask-1;v&=w[i];}return v;}
int score(const Circuit&c){std::array<U,128>w;for(int i=0;i<n;i++)w[i]=ins[i];for(int j=0;j<k;j++){if(!c.a[j]||!c.b[j])return 999;U a=product(c.a[j],w),b=product(c.b[j],w);if(j==c.bypass)w[n+j]=a;else{if(!(a&~b&target)||!(b&~a&target))return 999;w[n+j]=a|b;}}if(!c.out)return 999;return std::popcount(product(c.out,w)^target);}
void show(const Circuit&c,int s,U iter,double sec){std::cout<<"BEST errors="<<s<<" iterations="<<iter<<" seconds="<<sec<<" bypass="<<c.bypass<<" out="<<c.out<<std::endl;for(int j=0;j<k;j++)std::cout<<j<<" "<<c.a[j]<<" "<<c.b[j]<<"\n";std::cout.flush();}
int main(int argc,char**argv){std::ifstream f(argv[1]);f>>n>>k>>rows>>target;ones=(U(1)<<rows)-1;for(int i=0;i<n;i++)f>>ins[i];Circuit base;for(int j=0;j<k;j++)f>>base.a[j]>>base.b[j];f>>base.out;rngstate=std::strtoull(argv[3],nullptr,10);double limit=std::atof(argv[2]);auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};int best=999;U iter=0,restarts=0;
 while(elapsed()<limit){Circuit c=base;c.bypass=rnd()%k;if(rnd()%2)c.a[c.bypass]=c.b[c.bypass];int cs=score(c);if(cs==999)continue;restarts++;
  for(int step=0;step<40000;step++){iter++;Circuit d=c;int j=rnd()%(k+1);if(rnd()%40==0)d.bypass=rnd()%k;else{U* mask=j==k?&d.out:(rnd()%2?&d.a[j]:&d.b[j]);int width=n+j;*mask^=U(1)<<(rnd()%width);if(rnd()%4==0)*mask^=U(1)<<(rnd()%width);}int ds=score(d);double temp=0.04+0.9*(1.0-double(step)/40000);bool accept=ds<=cs||(ds<999&&double(rnd()>>11)*(1.0/9007199254740992.0)<std::exp(double(cs-ds)/temp));if(accept){c=d;cs=ds;}if(cs<best){best=cs;show(c,best,iter,elapsed());if(best==0){std::cout<<"FOUND 19-OR exact Fano boundary circuit; reconstruct and validate all assignments"<<std::endl;return 42;}}if((iter&1048575)==0&&elapsed()>=limit)break;}
 }
 std::cout<<"DONE iterations="<<iter<<" restarts="<<restarts<<" best="<<best<<" seconds="<<elapsed()<<std::endl;
}
