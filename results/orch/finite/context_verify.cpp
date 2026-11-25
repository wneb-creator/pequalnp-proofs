#include <cstdint>
#include <iostream>
#include <vector>
#include <chrono>
using namespace std;using U=uint64_t;
struct Gate{int op,a,b;U value;};
int main(){
 U base[16]={};for(int i=0;i<6;i++)for(int x=0;x<64;x++)if(x>>i&1)base[i]|=U(1)<<x;
 base[6]=base[0]|base[1];base[7]=base[2]|base[4];base[8]=base[7]|base[3];base[9]=base[8]|base[5];
 base[10]=base[0]|base[2];base[11]=base[10]|base[3];base[12]=base[1]|base[4];base[13]=base[12]|base[5];base[14]=0;base[15]=~U(0);
 U target=(base[0]&(base[4]|base[5]))|(base[1]&(base[2]|base[3]));
 cout<<"UPPER_VALID "<<(((base[6]&base[9])&(base[11]&base[13]))==target)<<"\n";
 U vals[19];for(int i=0;i<16;i++)vals[i]=base[i];Gate gs[3];long long nodes[3]={},hits[3]={},starhits[3]={};auto start=chrono::steady_clock::now();
 auto profile=[&](int depth){unsigned cones[3]={};int points[4]={17,33,6,10};for(int j=0;j<depth;j++){for(int w:{gs[j].a,gs[j].b})if(w>=16)cones[j]|=cones[w-16]|(1U<<(w-16));}
  for(int j=0;j<depth;j++)if(!gs[j].op){int owned=0;for(int e=0;e<4;e++)if(gs[j].value>>points[e]&1){bool prior=0;for(int i=0;i<j;i++)if((cones[j]>>i&1)&&!gs[i].op&&(gs[i].value>>points[e]&1))prior=1;if(!prior)owned|=1<<e;}if((owned&3)&&(owned&12))return false;}return true;};
 auto search=[&](auto&&self,int j,int limit)->void{
  int count=16+j;for(int op=0;op<2;op++)for(int a=0;a<count;a++)for(int b=a;b<count;b++){
   U value=op?(vals[a]|vals[b]):(vals[a]&vals[b]);bool duplicate=0;for(int i=0;i<count;i++)if(vals[i]==value){duplicate=1;break;}if(duplicate)continue;
   gs[j]={op,a,b,value};vals[count]=value;nodes[j]++;
   if(value==target){hits[j]++;if(profile(j+1)){starhits[j]++;cout<<"STAR_WITNESS "<<j+1<<"\n";for(int k=0;k<=j;k++)cout<<k<<" "<<gs[k].op<<" "<<gs[k].a<<" "<<gs[k].b<<"\n";}}
   if(j+1<limit)self(self,j+1,limit);
  }
 };
 search(search,0,2);cout<<"LOWER_COMPUTING_HITS "<<hits[0]<<" "<<hits[1]<<"\n";
 if(hits[0]||hits[1])return 2;
 for(int i=0;i<3;i++)nodes[i]=hits[i]=starhits[i]=0;
 search(search,0,3);
 cout<<"NODES "<<nodes[0]<<" "<<nodes[1]<<" "<<nodes[2]<<"\n";
 cout<<"COMPUTING_HITS "<<hits[0]<<" "<<hits[1]<<" "<<hits[2]<<"\n";
 cout<<"STAR_HITS "<<starhits[0]<<" "<<starhits[1]<<" "<<starhits[2]<<"\n";
 cout<<"SECONDS "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
