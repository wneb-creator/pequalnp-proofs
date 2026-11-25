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
int P=17;
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
array<V,2> gradients(const V&a){array<V,2>g{};for(auto&t:terms)for(int r=0;r<4;r++){int other[3],n=0;for(int k=0;k<4;k++)if(k!=r)other[n++]=a[t[k]];int x=other[0],y=other[1],z=other[2];g[0][t[r]]+=x*y+x*z+y*z;g[1][t[r]]+=x*y*z;}for(auto&v:g)for(int&x:v)x=mod(x);return g;}
int dot(const V&a,const V&b){int s=0;for(int k=0;k<10;k++)s+=a[k]*b[k];return mod(s);}
bool compatible(const D&a,const D&b,const array<V,2>&g){if(bil(a,b)||dot(g[0],b.v)||dot(g[1],b.v))return false;for(int l=1;l<=3;l++){auto c=coeff34(add(a.v,b.v,l));if(c[1]||(l<=2&&c[0]))return false;}return true;}
vector<V> rref(vector<V> rows){int r=0;for(int c=0;c<10&&r<(int)rows.size();c++){int pivot=r;while(pivot<(int)rows.size()&&!rows[pivot][c])pivot++;if(pivot==(int)rows.size())continue;swap(rows[r],rows[pivot]);int x=inv(rows[r][c]);for(int j=0;j<10;j++)rows[r][j]=mod(rows[r][j]*x);for(int i=0;i<(int)rows.size();i++)if(i!=r){x=rows[i][c];for(int j=0;j<10;j++)rows[i][j]=mod(rows[i][j]-x*rows[r][j]);}r++;}rows.resize(r);return rows;}
bool good3(const vector<V>&bs){for(int a=0;a<P;a++)for(int b=0;b<P;b++){V x=add(add(bs[0],bs[1],a),bs[2],b);if(!good(x))return false;}return true;}
void print(const V&a){cout<<'[';for(int i=0;i<10;i++){if(i)cout<<',';cout<<a[i];}cout<<']';}
int diagRank(const vector<V>&bs){vector<V>d=bs;for(auto &r:d)for(int k=0;k<10;k++)if(ij[k].first!=ij[k].second)r[k]=0;return rref(d).size();}

using X=array<int,8>;
vector<vector<int>> sqrt_table;
vector<int> inv_table;
V embed(const X&x){V v{};for(int i=0;i<8;i++)v[i]=x[i];v[8]=mod(-v[1]-v[2]-v[3]-v[5]-v[6]);v[9]=mod(-v[0]-v[4]-v[7]);return v;}
vector<X> kernel(vector<X> rows){
 int r=0;vector<int> pivots;
 for(int c=0;c<8&&r<(int)rows.size();c++){
  int k=r;while(k<(int)rows.size()&&!rows[k][c])k++;
  if(k==(int)rows.size())continue;
  swap(rows[r],rows[k]);int t=inv_table[rows[r][c]];
  for(int j=0;j<8;j++)rows[r][j]=mod(t*rows[r][j]);
  for(int i=0;i<(int)rows.size();i++)if(i!=r){t=rows[i][c];for(int j=0;j<8;j++)rows[i][j]=mod(rows[i][j]-t*rows[r][j]);}
  pivots.push_back(c);r++;
 }
 vector<X> basis;
 for(int c=0;c<8;c++)if(find(pivots.begin(),pivots.end(),c)==pivots.end()){
  X x{};x[c]=1;for(int i=0;i<r;i++)x[pivots[i]]=mod(-rows[i][c]);basis.push_back(x);
 }
 return basis;
}
template<class Callback> long long isotropic(vector<V> bs,Callback callback){
 int n=bs.size();if(!n)return 0;
 vector<D> ds;for(auto&b:bs)ds.push_back(data(b));
 int pivot=-1;
 for(int i=0;i<n;i++)if(bil(ds[i],ds[i])){pivot=i;break;}
 if(pivot<0){
  bool found=false;
  for(int i=0;i<n&&!found;i++)for(int j=i+1;j<n&&!found;j++)if(bil(ds[i],ds[j])){bs[i]=add(bs[i],bs[j]);ds[i]=data(bs[i]);pivot=i;found=true;}
 }
 if(pivot>=0){swap(bs[pivot],bs[n-1]);swap(ds[pivot],ds[n-1]);}
 int G[8][8]{};for(int i=0;i<n;i++)for(int j=0;j<n;j++)G[i][j]=bil(ds[i],ds[j]);
 int free_n=pivot>=0?n-1:n;long long emitted=0;
 for(int lead=0;lead<free_n;lead++){
  long long total=1;for(int j=lead+1;j<free_n;j++)total*=P;
  for(long long code=0;code<total;code++){
   int x[8]{};x[lead]=1;long long codeleft=code;
   for(int j=lead+1;j<free_n;j++){x[j]=codeleft%P;codeleft/=P;}
   auto emit=[&](int last){
    if(pivot>=0)x[n-1]=last;
    V v{};for(int c=0;c<10;c++){int s=0;for(int j=lead;j<n;j++)s+=x[j]*bs[j][c];v[c]=mod(s);}
    emitted++;callback(v);
   };
   if(pivot<0){emit(0);continue;}
   int qc=0,qb=0;
   for(int i=lead;i<free_n;i++){qb+=x[i]*G[i][n-1];qc+=x[i]*x[i]*G[i][i];for(int j=i+1;j<free_n;j++)qc+=2*x[i]*x[j]*G[i][j];}
   qc=mod(qc);qb=mod(2*qb);int qa=G[n-1][n-1];int disc=mod(qb*qb-4*qa*qc);int factor=inv_table[mod(2*qa)];
   for(int root:sqrt_table[disc])emit(mod((root-qb)*factor));
  }
 }
 return emitted;
}
void json_planes(const string&path,const set<vector<V>>&planes){
 ofstream f(path);f<<"[\n";bool first=true;
 for(auto&plane:planes){if(!first)f<<",\n";first=false;f<<'[';for(int r=0;r<2;r++){if(r)f<<',';f<<'[';for(int c=0;c<10;c++){if(c)f<<',';f<<plane[r][c];}f<<']';}f<<']';}f<<"\n]\n";
}
int main(int argc,char**argv){
 if(argc<3){cerr<<"usage: tracezero_census PRIME OUTPUT_PREFIX\n";return 2;}
 P=stoi(argv[1]);string prefix=argv[2];if(P<5||P>29)return 3;
 sqrt_table.resize(P);inv_table.resize(P);for(int x=0;x<P;x++){sqrt_table[x*x%P].push_back(x);if(x)inv_table[x]=inv(x);}
 int index[4][4];for(int k=0;k<10;k++){auto[i,j]=ij[k];index[i][j]=index[j][i]=k;}
 array<int,4>per{0,1,2,3};do{terms.push_back({index[0][per[0]],index[1][per[1]],index[2][per[2]],index[3][per[3]]});}while(next_permutation(per.begin(),per.end()));
 auto start=chrono::steady_clock::now();vector<V> standard;for(int i=0;i<8;i++){X x{};x[i]=1;standard.push_back(embed(x));}
 vector<D> dirs;
 long long quadratic_dirs=isotropic(standard,[&](const V&v){auto cp=coeff34(v);if(!cp[0]&&!cp[1])dirs.push_back(data(v));});
 cout<<"P="<<P<<" isotropic_projective_directions="<<quadratic_dirs<<" valid_tracezero_directions="<<dirs.size()<<" enumeration_seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 set<vector<V>> planes;long long candidates=0,good_candidates=0,compatible_count=0;array<long long,9> quotient_dims{};array<long long,3> diag_counts{};
 #pragma omp parallel for schedule(dynamic,32) num_threads(4) reduction(+:candidates,good_candidates,compatible_count)
 for(int i=0;i<(int)dirs.size();i++){
  const D&A=dirs[i];auto g=gradients(A.v);vector<X> constraints(4);int pivot=0;while(!A.v[pivot])pivot++;
  for(int j=0;j<8;j++){constraints[0][j]=bil(A,data(standard[j]));constraints[1][j]=dot(g[0],standard[j]);constraints[2][j]=dot(g[1],standard[j]);}constraints[3][pivot]=1;
  auto xb=kernel(constraints);vector<V> vb;for(auto&x:xb)vb.push_back(embed(x));
  #pragma omp atomic
  quotient_dims[xb.size()]++;
  candidates+=isotropic(vb,[&](const V&B){
   auto cp=coeff34(B);if(cp[0]||cp[1])return;good_candidates++;
   cp=coeff34(add(A.v,B));if(cp[0]||cp[1])return;
   cp=coeff34(add(A.v,B,2));if(cp[1])return;
   compatible_count++;auto basis=rref({A.v,B});if(basis.size()!=2){cerr<<"INTERNAL_DEPENDENCE_ERROR\n";abort();}
   #pragma omp critical
   planes.insert(basis);
  });
  if(i%5000==0){
   #pragma omp critical
   cerr<<"progress "<<i<<'/'<<dirs.size()<<" planes="<<planes.size()<<endl;
  }
 }
 for(auto&plane:planes)diag_counts[diagRank(plane)]++;
 json_planes(prefix+"-2planes.json",planes);
 cout<<"quotient_dimension_counts=";for(int i=0;i<9;i++)if(quotient_dims[i])cout<<i<<':'<<quotient_dims[i]<<' ';cout<<endl;
 cout<<"pair_candidates="<<candidates<<" good_pair_candidates="<<good_candidates<<" compatible_incidence_count="<<compatible_count<<endl;
 cout<<"tracezero_2planes="<<planes.size()<<" diagonal_rank_counts="<<diag_counts[0]<<','<<diag_counts[1]<<','<<diag_counts[2]<<" elapsed_seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 if(compatible_count!=(long long)planes.size()*(P+1)){cerr<<"INCIDENCE_COUNT_MISMATCH\n";return 4;}
 cout<<"INCIDENCE_AUDIT_PASS\n";return 0;
}
