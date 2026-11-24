#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using U=uint32_t;using Key=uint64_t;
std::array<std::array<int,32>,10> maps;
std::unordered_map<U,std::array<U,10>> trans;
auto const& tr(U v){auto it=trans.find(v);if(it!=trans.end())return it->second;std::array<U,10>a{};for(int p=0;p<10;p++)for(int x=0;x<32;x++)if(v&(U(1)<<x))a[p]|=U(1)<<maps[p][x];return trans.emplace(v,a).first->second;}
Key key(U a,U b){if(a>b)std::swap(a,b);return (Key(a)<<32)|b;}
Key canon(U a,U b){Key k=key(a,b);for(int p=1;p<10;p++)k=std::min(k,key(tr(a)[p],tr(b)[p]));return k;}
void unique(std::vector<U>&v){std::sort(v.begin(),v.end());v.erase(std::unique(v.begin(),v.end()),v.end());}
int main(){
 for(int p=0;p<10;p++)for(int x=0;x<32;x++)for(int i=0;i<5;i++)if(x>>i&1)maps[p][x]|=1<<((p<5?(i+p):(p-5-i+10))%5);
 std::vector<U> atom;for(int i=0;i<5;i++){U a=0;for(int x=0;x<32;x++)if(x>>i&1)a|=U(1)<<x;atom.push_back(a);}
 std::vector<U> clauses;for(int s=0;s<32;s++){U a=0;for(int i=0;i<5;i++)if(s>>i&1)a|=atom[i];clauses.push_back(a);}unique(clauses);
 U target=0;for(int x=0;x<32;x++){bool yes=true;for(int i=0;i<5;i++)if(!(x>>i&1)&&!(x>>((i+1)%5)&1))yes=false;if(yes)target|=U(1)<<x;}
 std::vector<U> first;for(U a:clauses)for(U b:clauses){U v=a&b;if(!std::binary_search(clauses.begin(),clauses.end(),v))first.push_back(v);}unique(first);
 std::unordered_set<Key> states;
 for(U a:first){std::vector<U> av=clauses;for(U c:clauses)av.push_back(a|c);unique(av);for(size_t i=0;i<av.size();i++)for(size_t j=0;j<=i;j++){U b=av[i]&av[j];if(b==target || (a|b)==target){std::cout<<"FAIL two OR gates suffice, dual first="<<a<<" second="<<b<<std::endl;return 1;}if(!std::binary_search(av.begin(),av.end(),b))states.insert(canon(a,b));}}
 std::cout<<"First AND functions="<<first.size()<<" second-stage symmetry classes="<<states.size()<<std::endl;
 unsigned long long tests=0;
 for(Key k:states){U a=U(k>>32),b=U(k);U q=0;if(!(a&~target))q|=a;if(!(b&~target))q|=b;U need=target&~q;
  std::vector<U> av;for(U c:clauses)for(U extra:{U(0),a,b,a|b}){U v=c|extra;if((need&~v)==0)av.push_back(v);}unique(av);
  for(size_t i=0;i<av.size();i++)for(size_t j=0;j<=i;j++){tests++;U v=av[i]&av[j];if(!(v&~target)){std::cout<<"FAIL three ORs suffice; dual a="<<a<<" b="<<b<<" u="<<av[i]<<" v="<<av[j]<<" q="<<q<<std::endl;return 1;}}
 }
 std::cout<<"PASS C5 requires at least four OR gates even allowing arbitrarily many AND gates. Last-gate pair tests="<<tests<<std::endl;
}
