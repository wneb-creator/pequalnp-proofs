#include <initializer_list>
#include <cstdint>
#include <cstdio>
int main(){
 using U=std::uint64_t;
 U var[6]={},orr[64]={};
 for(int i=0;i<6;i++)for(int s=0;s<64;s++)if((s>>i)&1)var[i]|=U(1)<<s;
 for(int a=0;a<64;a++)for(int i=0;i<6;i++)if((a>>i)&1)orr[a]|=var[i];
 U diag=(U(1)<<9)|(U(1)<<18)|(U(1)<<36);
 for(int extra: {0,98,140}){
  U goal=0;
  for(int s=0;s<64;s++)for(int i=0;i<3;i++)for(int j=0;j<3;j++)
   if((i==j || ((extra>>(3*i+j))&1))&&((s>>i)&1)&&((s>>(j+3))&1))goal|=U(1)<<s;
  bool found=false;
  for(int c=1;c<64&&!found;c++)for(int d=c;d<64&&!found;d++){
   U g0=orr[c]&orr[d];if(!(g0&~goal))continue;
   for(int b=0;b<64&&!found;b++){
    U rt=orr[b]|g0;if((rt&diag)!=diag)continue; U forbidden=rt&~goal;
    int a=0;for(int v=0;v<6;v++)if(!(var[v]&forbidden))a|=1<<v;
    for(int f=1;f<64&&!found;f++){
     if(g0&orr[f]&forbidden)continue;
     for(int e=0;e<64&&!found;e++){
      U g1=(g0|orr[e])&orr[f];if(!(g1&~goal)||g1&forbidden)continue;
      if(((g1|orr[a])&diag)==diag){
       std::printf("extra=%d a=%d b=%d c=%d d=%d e=%d f=%d\n",extra,a,b,c,d,e,f);found=true;
      }
     }
    }
   }
  }
  if(!found)std::printf("extra=%d no dependent opposite-side witness\n",extra);
 }
}
