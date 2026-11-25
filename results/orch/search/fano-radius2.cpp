#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
using U=uint64_t;
struct Gate{int op,a,b;};
struct Circuit{std::array<Gate,64>g;int bypass;};
int n,k,rows;U target;std::array<U,64>ins;
int score(const Circuit&c){std::array<U,128>w;std::array<int,128>col;for(int i=0;i<n;i++){w[i]=ins[i];col[i]=i<7?1:2;}for(int j=0;j<k;j++){auto g=c.g[j];int m=n+j;if(j==c.bypass){w[m]=w[g.a];col[m]=col[g.a];}else if(g.op){w[m]=w[g.a]|w[g.b];col[m]=col[g.a]|col[g.b];if(col[m]==3)return 999;}else{w[m]=w[g.a]&w[g.b];col[m]=0;}}return std::popcount(w[n+k-1]^target);}
int main(int argc,char**argv){std::ifstream f(argv[1]);f>>n>>k>>rows>>target;for(int i=0;i<n;i++)f>>ins[i];Circuit base;for(int j=0;j<k;j++)f>>base.g[j].op>>base.g[j].a>>base.g[j].b;U tried=0,valid=0;int best=999;auto start=std::chrono::steady_clock::now();
 for(int b=0;b<k;b++)for(int source=0;source<n+b;source++){
  Circuit c=base;c.bypass=b;c.g[b].a=source;
  for(int j=0;j<k;j++)if(j!=b)for(int x=0;x<n+j;x++)for(int y=x;y<n+j;y++)for(int op=0;op<2;op++){
   c.g[j]={op,x,y};tried++;int s=score(c);if(s!=999)valid++;best=std::min(best,s);
   if(s==0){std::cout<<"FOUND bypass="<<b<<" source="<<source<<" modified="<<j<<std::endl;for(int q=0;q<k;q++)std::cout<<q<<" "<<c.g[q].op<<" "<<c.g[q].a<<" "<<c.g[q].b<<"\n";return 42;}
   c.g[j]=base.g[j];
  }
 }
 std::cout<<"Complete radius-two search: tried="<<tried<<" valid_tCount0="<<valid<<" best_boundary_errors="<<best<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
