#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <vector>

using Profile = std::array<std::uint64_t,12>;
struct Hash {
  std::size_t operator()(const Profile& a) const {
    std::uint64_t h=0x9e3779b97f4a7c15ULL;
    for(auto x:a) {x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;
      x*=0x94d049bb133111ebULL;x^=x>>31;h^=x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}
    return h;
  }
};
int main(int argc,char**argv){
  if(argc!=3){std::cerr<<"usage: pair_closure profile_words.txt proper_productions.txt\n";return 2;}
  std::ifstream in(argv[1]);std::ofstream out(argv[2]);
  std::size_t n;in>>n;if(!in||!out||n<26)return 2;
  std::vector<Profile> a(n);std::unordered_map<Profile,int,Hash> ids;ids.reserve(2*n);
  for(std::size_t i=0;i<n;++i){for(auto&x:a[i])in>>x;if(!in)return 2;
    if(!ids.emplace(a[i],i).second)return 3;}
  std::uint64_t count[2]={0,0};Profile v;
  for(std::size_t i=0;i<n;++i)for(std::size_t j=i+1;j<n;++j)for(int op=0;op<2;++op){
    for(int k=0;k<12;++k)v[k]=op?(a[i][k]|a[j][k]):(a[i][k]&a[j][k]);
    if(v==a[i]||v==a[j])continue;
    auto it=ids.find(v);if(it==ids.end()||it->second<26)continue;
    out<<it->second<<' '<<op<<' '<<i<<' '<<j<<'\n';++count[op];
  }
  std::cout<<"{\"profiles\":"<<n<<",\"proper_and\":"<<count[0]<<",\"proper_or\":"<<count[1]<<",\"proper_total\":"<<count[0]+count[1]<<"}\n";
  return out?0:4;
}
