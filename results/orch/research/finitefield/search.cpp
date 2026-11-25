#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
int P=5;
using V=array<int,10>;
struct D { V v; array<int,4> row; };
array<pair<int,int>,10> ij{{{0,0},{0,1},{0,2},{0,3},{1,1},{1,2},{1,3},{2,2},{2,3},{3,3}}};
vector<array<int,4>> terms;
int mod(int x) {x%=P; return x<0?x+P:x;}
int inv(int a){for(int b=1;b<P;b++)if(a*b%P==1)return b;return 0;}
D data(V a){ D d{a,{0,0,0,0}}; for(int k=0;k<10;k++){auto [i,j]=ij[k];d.row[i]+=a[k];if(i!=j)d.row[j]+=a[k];}for(int&r:d.row)r=mod(r);return d;}
int bil(const D&a,const D&b){int s=0;for(int k=0;k<10;k++)s+=(ij[k].first==ij[k].second?1:2)*a.v[k]*b.v[k];for(int k=0;k<4;k++)s-=2*a.row[k]*b.row[k];return mod(s);}
array<int,2> coeff34(const V&a){int c3=0,c4=0;for(auto&t:terms){int x=a[t[0]],y=a[t[1]],z=a[t[2]],w=a[t[3]];c3+=x*y*z+x*y*w+x*z*w+y*z*w;c4+=x*y*z*w;}return {mod(c3),mod(c4)};}
V add(const V&a,const V&b,int c=1){V r;for(int i=0;i<10;i++)r[i]=mod(a[i]+c*b[i]);return r;}
bool good(const V&a){D d=data(a);if(bil(d,d))return false;auto c=coeff34(a);return !c[0]&&!c[1];}
bool compatible(const D&a,const D&b){if(bil(a,b))return false;for(int l=1;l<=3;l++){auto c=coeff34(add(a.v,b.v,l));if(c[1]||(l<=2&&c[0]))return false;}return true;}
vector<V> rref(vector<V> rows){int r=0;for(int c=0;c<10&&r<(int)rows.size();c++){int pivot=r;while(pivot<(int)rows.size()&&!rows[pivot][c])pivot++;if(pivot==(int)rows.size())continue;swap(rows[r],rows[pivot]);int x=inv(rows[r][c]);for(int j=0;j<10;j++)rows[r][j]=mod(rows[r][j]*x);for(int i=0;i<(int)rows.size();i++)if(i!=r){x=rows[i][c];for(int j=0;j<10;j++)rows[i][j]=mod(rows[i][j]-x*rows[r][j]);}r++;}rows.resize(r);return rows;}
bool good3(const vector<V>&bs){for(int a=0;a<P;a++)for(int b=0;b<P;b++){V x=add(add(bs[0],bs[1],a),bs[2],b);if(!good(x))return false;}return true;}
void print(const V&a){cout<<'[';for(int i=0;i<10;i++){if(i)cout<<',';cout<<a[i];}cout<<']';}
int diagRank(const vector<V>&bs){vector<V>d=bs;for(auto &r:d)for(int k=0;k<10;k++)if(ij[k].first!=ij[k].second)r[k]=0;return rref(d).size();}
int main(int argc,char**argv){if(argc>1)P=stoi(argv[1]);string prefix=argc>2?argv[2]:"finite";int index[4][4];for(int k=0;k<10;k++){auto[i,j]=ij[k];index[i][j]=index[j][i]=k;}array<int,4>p{0,1,2,3};do{terms.push_back({index[0][p[0]],index[1][p[1]],index[2][p[2]],index[3][p[3]]});}while(next_permutation(p.begin(),p.end()));
 auto start=chrono::steady_clock::now();vector<D> dirs;long long tested=0;for(int lead=0;lead<9;lead++){long long total=1;for(int k=lead+1;k<9;k++)total*=P;for(long long code=0;code<total;code++){V a{};a[lead]=1;long long z=code;for(int k=lead+1;k<9;k++){a[k]=z%P;z/=P;}int s=0;for(int k=0;k<9;k++)s+=(ij[k].first==ij[k].second?1:2)*a[k];a[9]=mod(-s);tested++;if(good(a))dirs.push_back(data(a));}}cout<<"P="<<P<<" tested="<<tested<<" good_projective_directions="<<dirs.size()<<endl;
 ofstream ds(prefix+"-directions.txt");for(auto&d:dirs){for(int x:d.v)ds<<x<<' ';ds<<'\n';}ds.close();
 vector<vector<int>> adj(dirs.size());long long edges=0;for(int i=0;i<(int)dirs.size();i++){for(int j=i+1;j<(int)dirs.size();j++)if(compatible(dirs[i],dirs[j])){adj[i].push_back(j);adj[j].push_back(i);edges++;}if(i%500==0)cerr<<"graph "<<i<<'/'<<dirs.size()<<" edges="<<edges<<endl;}for(auto&a:adj)sort(a.begin(),a.end());cout<<"compatible_edges="<<edges<<endl;
 ofstream es(prefix+"-edges.txt");for(int i=0;i<(int)dirs.size();i++)for(int j:adj[i])if(j>i)es<<i<<' '<<j<<'\n';es.close();
 set<vector<V>> planes;long long indep=0,triples=0;for(int i=0;i<(int)dirs.size();i++)for(int j:adj[i])if(j>i){vector<int>common;set_intersection(adj[i].begin(),adj[i].end(),adj[j].begin(),adj[j].end(),back_inserter(common));for(int k:common)if(k>j){triples++;vector<V>bs=rref({dirs[i].v,dirs[j].v,dirs[k].v});if(bs.size()!=3)continue;indep++;if(indep<=20){cout<<"INDEPENDENT "<<indep<<" diag_rank="<<diagRank(bs)<<" basis=";for(auto&a:bs)print(a);cout<<endl;}if(planes.count(bs)||!good3(bs))continue;planes.insert(bs);cout<<"PLANE "<<planes.size()<<" diag_rank="<<diagRank(bs)<<" basis=";for(auto&a:bs)print(a);cout<<endl;}}
 cout<<"triangles="<<triples<<" independent_compatible_triples="<<indep<<" good_3planes="<<planes.size()<<" elapsed_s="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
