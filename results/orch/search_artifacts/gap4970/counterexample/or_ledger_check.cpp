#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>
struct Gate {int op,a,b;};
int n,depth,full;uint16_t wire[16];Gate gates[12];
int pure[65536],support[65536];
std::vector<unsigned>parts;std::map<unsigned,int>index;
int trans[64][16],ranks[64];
unsigned long long visited[12]={};bool found=false;

unsigned merge(unsigned state,int q){
 unsigned block=0;
 for(int i=0;i<n;i++)if(q>>i&1)block|=(state>>(4*i))&15;
 for(int i=0;i<n;i++)if(block>>i&1){state&=~(15u<<(4*i));state|=block<<(4*i);}
 return state;
}
void dfs(int j,const std::array<unsigned char,16>&state,const std::array<unsigned char,16>&counts){
 if(j==depth||found)return;
 for(int a=0;a<n+j;a++)for(int b=a;b<n+j;b++)for(int op=0;op<2;op++){
  gates[j]={op,a,b};wire[n+j]=op?(wire[a]|wire[b]):(wire[a]&wire[b]);visited[j+1]++;
  auto next=state,ct=counts;int fn=wire[n+j],q=pure[fn];
  for(int s=1;s<=full;s++){
   if(q>0&&(q&~s)==0)next[s]=trans[state[s]][q];
   if(op&&!(fn>>(full^s)&1)&&std::popcount((unsigned)support[fn])>=2)ct[s]++;
   if(ranks[next[s]]>ct[s]){
    found=true;std::printf("COUNTEREXAMPLE n=%d gates=%d S=%d rank=%d count=%d\n",n,j+1,s,ranks[next[s]],ct[s]);
    for(int k=0;k<=j;k++)std::printf("%d %c %d %d\n",n+k,"&|"[gates[k].op],gates[k].a,gates[k].b);
    return;
   }
  }
  dfs(j+1,next,ct);if(found)return;
 }
}
int main(int argc,char**argv){
 n=argc>1?std::atoi(argv[1]):3;depth=argc>2?std::atoi(argv[2]):5;if(n<1||n>4||depth>10)return 2;full=(1<<n)-1;
 for(int f=0;f<65536;f++){pure[f]=-1;support[f]=0;for(int i=0;i<n;i++)if(f>>(1<<i)&1)support[f]|=1<<i;}
 for(int q=0;q<=full;q++){int f=0;for(int r=0;r<=full;r++)if(r&q)f|=1<<r;pure[f]=q;}
 unsigned initial=0;for(int i=0;i<n;i++)initial|=(1u<<i)<<(4*i);parts.push_back(initial);index[initial]=0;
 for(unsigned k=0;k<parts.size();k++)for(int q=0;q<=full;q++){unsigned t=merge(parts[k],q);if(!index.count(t)){index[t]=parts.size();parts.push_back(t);}trans[k][q]=index[t];}
 for(unsigned k=0;k<parts.size();k++){int count=0;for(int i=0;i<n;i++){unsigned block=parts[k]>>(4*i)&15;if((block&((1u<<i)-1))==0)count++;}ranks[k]=n-count;}
 for(int i=0;i<n;i++)for(int r=0;r<=full;r++)if(r>>i&1)wire[i]|=1<<r;
 auto start=std::chrono::steady_clock::now();std::array<unsigned char,16>zero{};dfs(0,zero,zero);
 std::printf("n=%d max_gates=%d partitions=%zu counterexample=%d seconds=%.3f\n",n,depth,parts.size(),found,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());
 for(int i=1;i<=depth;i++)std::printf("circuits_%d=%llu\n",i,visited[i]);
 return found?1:0;
}
