#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
#include <chrono>
struct Example { std::array<int,14> r; std::vector<int> assigned; int maxold,maxnew; };
int main(int argc,char**argv){
 if(argc!=3&&argc!=4)return 2;
 int kind=std::stoi(argv[1]);if(kind<0||kind>2)return 2;
 std::vector<int>I=kind==0?std::vector<int>{0}:kind==1?std::vector<int>{0,1}:std::vector<int>{0,9};
 int units=kind==0?1:2,n=1<<units; const int ALL=(1<<14)-1,POINTS=(1<<7)-1,LINES=ALL^POINTS;
 int nb[14]={};int rows[7][3]={{7,8,10},{7,9,13},{8,12,13},{7,11,12},{10,11,13},{9,10,12},{8,9,11}};
 for(int i=0;i<7;i++)for(int j:rows[i]){nb[i]|=1<<j;nb[j]|=1<<i;}
 int E=ALL;for(int i:I)E^=1<<i;std::vector<int>es;for(int i=0;i<14;i++)if(E>>i&1)es.push_back(i);
 std::uint64_t total=1;for(int i:es){(void)i;total*=n;}
 std::uint64_t counts[5]={};std::vector<Example>examples;
 const std::uint64_t limit=argc==4?std::min<std::uint64_t>(total,std::stoull(argv[3])):total;
 auto start=std::chrono::steady_clock::now();
 for(std::uint64_t code=0;code<limit;code++){
  counts[0]++;std::uint64_t z=code;std::array<int,14>r={};int present=0,R[2]={};
  for(int i:es){r[i]=z%n;z/=n;present|=r[i];for(int j=0;j<units;j++)if(r[i]>>j&1)R[j]|=1<<i;}
  if(present!=n-1)continue;counts[1]++;
  int shared[14]={};for(int i:es)shared[i]=1<<i;
  for(int j=0;j<units;j++)for(int i:es)if(R[j]>>i&1)shared[i]|=R[j];
  std::vector<int>A;for(int i:I)A.push_back(nb[i]);
  for(int a:A)for(int x:es)if(a>>x&1)shared[x]|=a;
  bool changed=true;
  while(changed){changed=false;for(std::size_t k=0;k<I.size();k++){
   int a=A[k];for(int x:es)if(nb[I[k]]>>x&1)for(int t:es)
    if((r[x]&~r[t])==0&&(shared[x]>>t&1))a|=1<<t;
   if(a!=A[k]){changed=true;A[k]=a;for(int x:es)if(a>>x&1)shared[x]|=a;}
  }}
  bool ok=true;for(int t:es){int count=(nb[t]&E)?1:0;for(int a:A)count+=(a>>t)&1;if(count>2+__builtin_popcount((unsigned)r[t])){ok=false;break;}}
  if(!ok)continue;counts[2]++;
  int maxold=0,maxnew=0;
  for(int c:es){int X=0;for(int x:es)if(x!=c&&(r[x]&~r[c])==0&&(shared[x]>>c&1))X|=1<<x;
   int free=((c<7?LINES:POINTS)&~nb[c]&E&~X);int f=__builtin_popcount((unsigned)free);
   int cost=__builtin_popcount((unsigned)r[c])+__builtin_popcount((unsigned)X);
   int oldscore=cost+(f?8:7),newscore=cost+(f>=3?9:f?8:7);
   if(oldscore>maxold)maxold=oldscore;if(newscore>maxnew)maxnew=newscore;
  }
  if(maxold>14)continue;counts[3]++;
  if(maxnew>14)continue;counts[4]++;
  if(examples.size()<20)examples.push_back({r,A,maxold,maxnew});
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::ofstream o(argv[2]);o<<"{\n  \"ineligible\": [";for(std::size_t j=0;j<I.size();j++)o<<(j?", ":"")<<I[j];
 o<<"],\n  \"full_state_count\": "<<total<<",\n  \"units\": "<<units<<",\n  \"seconds\": "<<seconds<<",\n  \"counts_enumerated_nonempty_budget_oldcut_newcut\": [";
 for(int j=0;j<5;j++)o<<(j?", ":"")<<counts[j];o<<"],\n  \"first_survivors\": [\n";
 for(std::size_t j=0;j<examples.size();j++){auto&e=examples[j];o<<(j?",\n":"")<<"    {\"r\": [";for(int t=0;t<14;t++)o<<(t?", ":"")<<e.r[t];o<<"], \"assigned_bitmasks\": [";for(std::size_t k=0;k<e.assigned.size();k++)o<<(k?", ":"")<<e.assigned[k];o<<"], \"max_old_score\": "<<e.maxold<<", \"max_new_score\": "<<e.maxnew<<"}";}
 o<<"\n  ]\n}\n";
 std::cout<<"kind="<<kind<<" seconds="<<seconds<<" counts";for(auto c:counts)std::cout<<" "<<c;std::cout<<"\n";
}
