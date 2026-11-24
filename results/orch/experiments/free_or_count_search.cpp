#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <vector>
using U=uint64_t;
struct Target{U t,linear,graph;unsigned bound;};
int main(int argc,char**argv){
 int n=std::stoi(argv[1]);std::ifstream in(argv[2]);std::unordered_map<U,Target> exact;std::vector<Target> special;
 Target r;while(in>>r.t>>r.bound>>r.linear>>r.graph){if(r.linear==0)exact[r.t]=r;else special.push_back(r);}
 U full=n==6?~U(0):(U(1)<<(1<<n))-1;std::vector<U> atom;for(int i=0;i<n;i++){U a=0;for(int x=0;x<(1<<n);x++)if(x>>i&1)a|=U(1)<<x;atom.push_back(a);}
 std::vector<U> clauses;for(int s=0;s<(1<<n);s++){U v=0;for(int i=0;i<n;i++)if(s>>i&1)v|=atom[i];clauses.push_back(v);}
 unsigned long long checked=0;
 auto check=[&](U v,unsigned k){checked++;auto it=exact.find(v);if(it!=exact.end() && k<it->second.bound){std::cout<<"FAIL exact gates="<<k<<" graph="<<it->second.graph<<" target="<<v<<std::endl;return false;}
 for(auto const&t:special)if(k<t.bound && (v&~t.t)==0 && (v|t.linear)==t.t){std::cout<<"FAIL linear gates="<<k<<" graph="<<t.graph<<" target="<<t.t<<std::endl;return false;}return true;};
 for(U a:clauses)if(!check(a,0))return 1;
 std::vector<U> firsts{full};for(U a:clauses)for(U b:clauses)firsts.push_back(a&b);std::sort(firsts.begin(),firsts.end());firsts.erase(std::unique(firsts.begin(),firsts.end()),firsts.end());
 for(U a:firsts){if(!check(a,1))return 1;std::vector<U> available=clauses;for(U c:clauses)available.push_back(a|c);std::sort(available.begin(),available.end());available.erase(std::unique(available.begin(),available.end()),available.end());
 for(size_t i=0;i<available.size();i++)for(size_t j=0;j<=i;j++){U b=available[i]&available[j];if(!check(b,2)||!check(a|b,2))return 1;}}
 std::cout<<"PASS n="<<n<<" targets="<<exact.size()+special.size()<<" first_AND_functions="<<firsts.size()<<" output_candidates="<<checked<<". Exhaustive through two ANDs with arbitrary free OR gates."<<std::endl;
}
