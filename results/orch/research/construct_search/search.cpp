#include <array>
#include <complex>
#include <vector>
#include <algorithm>
#include <iostream>
#include <functional>
#include <fstream>
using Z=std::complex<long long>;
using M=std::array<Z,16>;
std::vector<std::array<int,4>> perms;
std::array<std::pair<int,int>,10> ij;
Z quad(const M&a){Z s=0,q=0;for(int i=0;i<4;i++){Z r=0;for(int j=0;j<4;j++){r+=a[4*i+j];q+=a[4*i+j]*a[4*i+j];}s+=r;q-=2LL*r*r;}return q+s*s;}
Z cubic(const M&a){Z c=0;for(auto p:perms){std::array<Z,4> x;for(int i=0;i<4;i++)x[i]=a[4*i+p[i]];for(int k=0;k<4;k++){Z z=1;for(int i=0;i<4;i++)if(i!=k)z*=x[i];c+=z;}}return c;}
Z quartic(const M&a){Z c=0;for(auto p:perms){Z z=1;for(int i=0;i<4;i++)z*=a[4*i+p[i]];c+=z;}return c;}
M add(const M&a,const M&b,long long k=1){M c;for(int i=0;i<16;i++)c[i]=a[i]+k*b[i];return c;}
bool compat(const M&a,const M&b){M c=add(a,b);if(quad(c)!=Z(0)||cubic(c)!=Z(0)||quartic(c)!=Z(0))return false;c=add(a,b,-1);if(cubic(c)!=Z(0)||quartic(c)!=Z(0))return false;return quartic(add(a,b,2))==Z(0);}
bool indep(const M&a,const M&b,const M&c){for(int i=0;i<16;i++)for(int j=i+1;j<16;j++){Z d=a[i]*b[j]-a[j]*b[i];if(d!=Z(0)){Z x=c[i]*b[j]-c[j]*b[i],y=a[i]*c[j]-a[j]*c[i];for(int k=0;k<16;k++)if(d*c[k]!=x*a[k]+y*b[k])return true;return false;}}return false;}
bool triple(const M&a,const M&b,const M&c){M s=add(add(a,b),c);return cubic(s)==Z(0)&&quartic(s)==Z(0)&&quartic(add(s,a,-2))==Z(0)&&quartic(add(s,b,-2))==Z(0);}
void show(const M&a){for(int i=0;i<4;i++){for(int j=0;j<4;j++)std::cout<<a[4*i+j]<<' ';std::cout<<'\n';}}
int main(int argc,char**argv){std::array<int,4> p{0,1,2,3};do{perms.push_back(p);}while(std::next_permutation(p.begin(),p.end()));int ix=0;for(int i=0;i<4;i++)for(int j=i;j<4;j++)ij[ix++]={i,j};
 std::vector<Z> vals{Z(0),Z(1),Z(-1),Z(0,1),Z(0,-1)};if(argc>1)vals={Z(0),Z(1),Z(-1),Z(2),Z(-2)};
 std::vector<M> good;M a{};long long count=0;
 std::function<void(int,Z,bool)> rec=[&](int k,Z s,bool started){if(k==9){Z last=-s;if(std::find(vals.begin(),vals.end(),last)==vals.end())return;a[15]=last;if(!started&&last!=Z(1)&&!(argc>1&&last==Z(2)))return;count++;if(quad(a)==Z(0)&&cubic(a)==Z(0)&&quartic(a)==Z(0))good.push_back(a);return;}auto [i,j]=ij[k];for(Z v:vals){if(!started&&v!=Z(0)&&v!=Z(1)&&!(argc>1&&v==Z(2)))continue;a[4*i+j]=a[4*j+i]=v;rec(k+1,s+(i==j?1LL:2LL)*v,started||v!=Z(0));}};rec(0,Z(0),false);
 std::cout<<"directions checked "<<count<<" good "<<good.size()<<std::endl;
 if(argc>2){std::ofstream f("/tmp/oec/pequalnp-pilot-78/construct_search/directions-real.txt");for(const auto&m:good){for(Z z:m)f<<z.real()<<' '<<z.imag()<<' ';f<<'\n';}}
 std::vector<std::vector<int>> adj(good.size());long long edges=0;for(int i=0;i<(int)good.size();i++){for(int j=i+1;j<(int)good.size();j++)if(compat(good[i],good[j])){adj[i].push_back(j);edges++;}if(i%100==0)std::cout<<"pairs row "<<i<<" edges "<<edges<<std::endl;}
 long long triangles=0,independent=0;for(int i=0;i<(int)good.size();i++)for(int j:adj[i]){std::vector<int> common;std::set_intersection(adj[i].begin(),adj[i].end(),adj[j].begin(),adj[j].end(),std::back_inserter(common));for(int k:common){triangles++;if(!indep(good[i],good[j],good[k]))continue;independent++;if(triple(good[i],good[j],good[k])){std::cout<<"FOUND "<<i<<' '<<j<<' '<<k<<'\n';show(good[i]);show(good[j]);show(good[k]);return 0;}}}
 std::cout<<"NO CANDIDATE edges "<<edges<<" triangles "<<triangles<<" independent "<<independent<<std::endl;
}
