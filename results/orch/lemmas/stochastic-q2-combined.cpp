#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <chrono>
#include <algorithm>
struct Family {int strict;std::array<int,7> masks;};
int main(int argc,char**argv){
 if(argc!=4)return 2;
 std::ifstream ri(argv[1]),fi(argv[2]);int nr,nf;ri>>nr;fi>>nf;std::vector<std::array<int,7>>rs(nr);std::vector<Family>fs(nf);
 for(auto&r:rs)for(int&x:r)ri>>x;
 for(auto&f:fs){fi>>f.strict;for(int&x:f.masks)fi>>x;}
 int N[7]={11,69,98,49,88,44,22},degree[7]={3,2,1,1,1,2,2};
 auto pc=[](int x){return __builtin_popcount((unsigned)x);};
 unsigned long long counts[5]={};int processed=0;auto start=std::chrono::steady_clock::now();
 std::ofstream out(argv[3]);out<<"{\n  \"examples\": [\n";int examples=0;
 for(auto&r:rs){
  int units[3]={};for(int j=0;j<3;j++)for(int t=0;t<7;t++)if(r[t]>>j&1)units[j]|=1<<t;
  bool exact[4]={};for(int i:{0,1,3})for(int x=0;x<7;x++)if(N[i]>>x&1)if(degree[x]>=2&&pc(r[x])<=1)exact[i]=true;
  for(auto&f:fs){
   counts[0]++;bool ok=true;
   auto has=[&](int mask){return std::find(f.masks.begin(),f.masks.end(),mask)!=f.masks.end();};
   for(int u:units)if(pc(u)>=3||(pc(u)==2&&((u&N[0])==u||(u&N[1])==u||(u&N[3])==u)))if(!has(u)){ok=false;break;}
   if(!ok)continue;counts[1]++;
   int shared[7]={};for(int t=0;t<7;t++)shared[t]=1<<t;
   auto add=[&](int mask){for(int t=0;t<7;t++)if(mask>>t&1)shared[t]|=mask;};
   for(int u:units)add(u);for(int u:f.masks)add(u);
   int A[4]={N[0],N[1],f.strict,N[3]};bool changed=true;
   while(changed&&ok){changed=false;for(int i=0;i<4;i++){
    int a=A[i];for(int x=0;x<7;x++)if(N[i]>>x&1)for(int t=0;t<7;t++)if((r[x]&~r[t])==0&&(shared[x]>>t&1))a|=1<<t;
    if((i==2&&(a&~f.strict))||(exact[i]&&(a&~N[i]))){ok=false;break;}
    bool fits=false;for(int mask:f.masks)if((a&~mask)==0){fits=true;break;}if(!fits){ok=false;break;}
    if(a!=A[i]){A[i]=a;add(a);changed=true;}
   }}
   if(!ok)continue;counts[2]++;
   for(int t=0;t<7;t++){int count=t==0?0:1;for(int a:A)count+=(a>>t)&1;if(count>2+pc(r[t])){ok=false;break;}}
   if(!ok)continue;counts[3]++;
   int cost[7]={};for(int c=0;c<7;c++){cost[c]=pc(r[c]);for(int x=0;x<7;x++)if(x!=c&&(r[x]&~r[c])==0&&(shared[x]>>c&1))cost[c]++;if(cost[c]>(c==0?5:6)){ok=false;break;}}
   if(!ok)continue;counts[4]++;
   if(examples<10000){out<<(examples?",\n":"")<<"    {\"r\": [";for(int t=0;t<7;t++)out<<(t?", ":"")<<r[t];out<<"], \"strict_mask\": "<<f.strict<<", \"family\": [";for(int t=0;t<7;t++)out<<(t?", ":"")<<f.masks[t];out<<"], \"assigned\": [";for(int i=0;i<4;i++)out<<(i?", ":"")<<A[i];out<<"], \"costs\": [";for(int t=0;t<7;t++)out<<(t?", ":"")<<cost[t];out<<"]}";examples++;}
  }
  processed++;if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>20)break;
 }
 double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 out<<"\n  ],\n  \"vectors_processed\": "<<processed<<",\n  \"vectors_total\": "<<nr<<",\n  \"families_each\": "<<nf<<",\n  \"complete\": "<<(processed==nr?"true":"false")<<",\n  \"seconds\": "<<elapsed<<",\n  \"counts_pairs_residual_family_closure_budget_cofactor\": [";for(int i=0;i<5;i++)out<<(i?", ":"")<<counts[i];out<<"]\n}\n";
 std::cout<<"vectors "<<processed<<"/"<<nr<<" families "<<nf<<" seconds "<<elapsed<<" counts";for(auto x:counts)std::cout<<" "<<x;std::cout<<"\n";
}
