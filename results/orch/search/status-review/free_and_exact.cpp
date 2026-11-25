#include <array>
#include <vector>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <chrono>
#include <unordered_set>
struct Step{uint64_t a,b,g;};
uint64_t target=0,pos=0;
int limit=4;uint64_t nodes=0,candidates=0;
std::array<Step,10> route;
auto began=std::chrono::steady_clock::now();
bool timeout=false;double maxSeconds=180.;
bool dfs(const std::vector<uint64_t>& s,int k){
 ++nodes;if((nodes&65535)==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>maxSeconds){timeout=true;return false;}
 if(std::binary_search(s.begin(),s.end(),target)){std::cout<<"FOUND cost="<<k<<"\n";for(int i=0;i<k;++i)std::cout<<route[i].a<<" | "<<route[i].b<<" = "<<route[i].g<<"\n";return true;}
 if(k==limit)return false;
 std::vector<uint64_t> supers;
 if(k+1==limit){for(auto x:s)if((x&target)==target)supers.push_back(x);supers.push_back(~0ULL);}
 std::unordered_set<uint64_t> seen;
 for(int a=0;a<(int)s.size();++a)for(int b=a+1;b<(int)s.size();++b){
  uint64_t g=s[a]|s[b];if(std::binary_search(s.begin(),s.end(),g))continue;
  if(!seen.insert(g).second)continue;++candidates;route[k]={s[a],s[b],g};
  if(k+1==limit){if((g&target)!=target)continue;for(auto x:supers)if((g&x)==target){std::cout<<"FOUND cost="<<k+1<<" output_AND="<<x<<"\n";for(int i=0;i<=k;++i)std::cout<<route[i].a<<" | "<<route[i].b<<" = "<<route[i].g<<"\n";return true;}continue;}
  std::vector<uint64_t> t=s;t.push_back(g);for(auto x:s){auto y=g&x;if(y&pos)t.push_back(y);}std::sort(t.begin(),t.end());t.erase(std::unique(t.begin(),t.end()),t.end());
  if(dfs(t,k+1))return true;if(timeout)return false;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc>1)limit=std::atoi(argv[1]);if(argc>2)maxSeconds=std::atof(argv[2]);
 std::array<uint64_t,6> v{};for(int i=0;i<6;++i)for(int x=0;x<64;++x)if(x>>i&1)v[i]|=1ULL<<x;
 std::vector<uint64_t>s(v.begin(),v.end());
 for(int i=0;i<3;++i)for(int j=0;j<3;++j)if(i!=j){target|=v[i]&v[3+j];pos|=1ULL<<((1<<i)|(1<<(3+j)));s.push_back(v[i]&v[3+j]);}
 std::sort(s.begin(),s.end());began=std::chrono::steady_clock::now();
 bool found=dfs(s,0);std::cout<<"limit="<<limit<<" found="<<found<<" timeout="<<timeout<<" nodes="<<nodes<<" candidates="<<candidates<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()<<"\n";
}
