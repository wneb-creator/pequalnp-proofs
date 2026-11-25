#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <chrono>
int main(int argc,char**argv){
 if(argc!=3)return 2;std::ifstream in(argv[1]);int nf;in>>nf;std::vector<std::array<int,8>>families(nf);for(auto&f:families)for(int&x:f)in>>x;
 int N[7]={11,69,98,49,88,44,22},degree[7]={3,2,1,1,1,2,2};auto pc=[](int x){return __builtin_popcount((unsigned)x);};unsigned long long counts[6]={},direct_before_protection=0,direct_after_protection=0;auto start=std::chrono::steady_clock::now();int processed=0,examples=0; bool domains[3][128]={}; unsigned long long centerhist[3][20]={};std::ofstream out(argv[2]);out<<"{\n  \"examples\": [\n";
 for(auto&f:families){
  std::vector<int>allowed={0};for(int t=0;t<7;t++)allowed.push_back(1<<t);for(int m=0;m<128;m++)if(pc(m)==2&&(m&N[0])!=m&&(m&N[1])!=m&&(m&N[3])!=m)allowed.push_back(m);for(int k=1;k<8;k++)allowed.push_back(f[k]);std::sort(allowed.begin(),allowed.end());allowed.erase(std::unique(allowed.begin(),allowed.end()),allowed.end());
  std::vector<int>opts[4];for(int i=0;i<4;i++)for(int k=1;k<8;k++)if((N[i]&~f[k])==0)opts[i].push_back(f[k]);
  for(int a0:opts[0])for(int a1:opts[1])for(int a2:opts[2])for(int a3:opts[3]){
   if(a2!=f[0])continue;int A[4]={a0,a1,a2,a3};int need[7]={};for(int t=0;t<7;t++){int c=t==0?0:1;for(int a:A)c+=(a>>t)&1;need[t]=std::max(0,c-2);}
   for(int u:allowed)for(int v:allowed)for(int w:allowed){
    counts[0]++;int unit[3]={u,v,w},r[7]={};for(int t=0;t<7;t++)for(int j=0;j<3;j++)if(unit[j]>>t&1)r[t]|=1<<j;
    bool ok=true;for(int t=0;t<7;t++)if(pc(r[t])<need[t]){ok=false;break;}if(!ok)continue;counts[1]++;
    int shared[7]={};for(int t=0;t<7;t++)shared[t]=1<<t;auto add=[&](int mask){for(int t=0;t<7;t++)if(mask>>t&1)shared[t]|=mask;};for(int x:unit)add(x);for(int k=1;k<8;k++)add(f[k]);
    for(int i=0;i<4&&ok;i++)for(int x=0;x<7&&ok;x++)if(N[i]>>x&1)for(int t=0;t<7;t++)if((r[x]&~r[t])==0&&(shared[x]>>t&1)&&!(A[i]>>t&1)){ok=false;break;}
    if(!ok)continue;counts[2]++;
    int c0=pc(r[0]);for(int x=1;x<7;x++)if((r[x]&~r[0])==0&&(shared[x]&1))c0++;if(c0<=5)direct_before_protection++; for(int z:unit)domains[0][z]=true; centerhist[0][c0]++;
    for(int i:{0,1,3})for(int x=0;x<7;x++)if(N[i]>>x&1)if(degree[x]>=2&&pc(r[x])<=1&&A[i]!=N[i])ok=false;if(!ok)continue;counts[3]++;if(c0<=5)direct_after_protection++; for(int z:unit)domains[1][z]=true; centerhist[1][c0]++;
    int costs[7]={};for(int c=0;c<7;c++){costs[c]=pc(r[c]);for(int x=0;x<7;x++)if(x!=c&&(r[x]&~r[c])==0&&(shared[x]>>c&1))costs[c]++;if(costs[c]>6)ok=false;}if(!ok)continue;counts[4]++; for(int z:unit)domains[2][z]=true; centerhist[2][c0]++;
    bool new_ok=costs[0]<=5;if(new_ok)counts[5]++;
    if(examples<20){out<<(examples?",\n":"")<<"    {\"unit_masks\": ["<<u<<", "<<v<<", "<<w<<"], \"strict_mask\": "<<f[0]<<", \"family\": [";for(int k=1;k<8;k++)out<<(k>1?", ":"")<<f[k];out<<"], \"assigned\": ["<<a0<<", "<<a1<<", "<<a2<<", "<<a3<<"], \"center_cost\": "<<costs[0]<<", \"passes_new_cut\": "<<(new_ok?"true":"false")<<"}";examples++;}
   }
  }
  processed++;if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>20)break;
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();out<<"\n  ],\n  \"families_processed\": "<<processed<<",\n  \"families_total\": "<<nf<<",\n  \"complete\": "<<(processed==nf?"true":"false")<<",\n  \"seconds\": "<<seconds<<",\n  \"direct_center_survivors_before_protection\": "<<direct_before_protection<<",\n  \"direct_center_survivors_after_protection\": "<<direct_after_protection<<",\n  \"counts_all_budget_colabel_protected_oldcofactor_newcofactor\": [";for(int i=0;i<6;i++)out<<(i?", ":"")<<counts[i];out<<"],\n  \"domains\": [";for(int stage=0;stage<3;stage++){out<<(stage?", ":"")<<"[";bool comma=false;for(int z=0;z<128;z++)if(domains[stage][z]){out<<(comma?", ":"")<<z;comma=true;}out<<"]";}out<<"],\n  \"center_cost_histograms\": [";for(int stage=0;stage<3;stage++){out<<(stage?", ":"")<<"{";bool comma=false;for(int z=0;z<20;z++)if(centerhist[stage][z]){out<<(comma?", ":"")<<"\""<<z<<"\": "<<centerhist[stage][z];comma=true;}out<<"}";}out<<"]\n}\n";std::cout<<"families "<<processed<<"/"<<nf<<" seconds "<<seconds<<" counts";for(auto x:counts)std::cout<<" "<<x;std::cout<<" direct_before "<<direct_before_protection<<" direct_after "<<direct_after_protection<<"\n";
}
