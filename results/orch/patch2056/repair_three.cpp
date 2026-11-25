#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using U=uint64_t;
using V=std::array<U,2>;
struct Gate {int op,a,b;};
using Net=std::vector<Gate>;
V comb(int op,V a,V b){return op?V{a[0]|b[0],a[1]|b[1]}:V{a[0]&b[0],a[1]&b[1]};}
std::vector<V> eval(const Net&c,const std::vector<V>&in){auto v=in;for(auto g:c)v.push_back(comb(g.op,v[g.a],v[g.b]));return v;}
int main(int argc,char**argv){
 if(argc!=6)return 2;int n=std::stoi(argv[3]),pos=std::stoi(argv[4]),ng=std::stoi(argv[5]);
 std::ifstream rf(argv[1]);std::vector<int>rows;int r;while(rf>>r)rows.push_back(r);if(rows.size()>128)return 3;
 std::vector<V>in(n);V target{},mask{};
 for(int k=0;k<(int)rows.size();k++){for(int i=0;i<n;i++)if(rows[k]>>i&1)in[i][k/64]|=U(1)<<(k%64);if(k<pos)target[k/64]|=U(1)<<(k%64);mask[k/64]|=U(1)<<(k%64);}
 std::ifstream f(argv[2]);Net c(ng);long long tested=0,parents=0,expressions=0;int batches=0;
 auto emit=[&](const Net&d){for(auto g:d)std::cout<<g.op<<' '<<g.a<<' '<<g.b<<'\n';std::cout.flush();};
 while(f>>c[0].op>>c[0].a>>c[0].b){for(int j=1;j<ng;j++)if(!(f>>c[j].op>>c[j].a>>c[j].b))return 4;batches++;
  for(int j=0;j<ng;j++)if(c[j].a<0||c[j].b<0||c[j].a>=n+j||c[j].b>=n+j)return 5;
  auto vals=eval(c,in);if(vals.back()==target){emit(c);return 0;}
  std::vector<int>uses(n+ng);for(auto g:c){uses[g.a]++;uses[g.b]++;}
  for(int j=0;j<ng;j++){
   std::array<V,2>outs;
   for(int b=0;b<2;b++){auto v=vals;v[n+j]=b?mask:V{};for(int k=j+1;k<ng;k++)v[n+k]=comb(c[k].op,v[c[k].a],v[c[k].b]);outs[b]=v.back();}
   V care{outs[0][0]^outs[1][0],outs[0][1]^outs[1][1]};
   if(((outs[0][0]^target[0])&~care[0]&mask[0])||((outs[0][1]^target[1])&~care[1]&mask[1]))continue;parents++;
   auto ok=[&](V v){expressions++;return !(((v[0]^target[0])&care[0])|((v[1]^target[1])&care[1]));};
   for(int a=0;a<n+j;a++)for(int b=a;b<n+j;b++)for(int op=0;op<2;op++)if(ok(comb(op,vals[a],vals[b]))){auto d=c;d[j]={op,a,b};tested++;if(eval(d,in).back()!=target)return 6;emit(d);std::cerr<<"FOUND single repair batch="<<batches<<" parent="<<j<<'\n';return 0;}
   std::set<int>hs;for(int h:{c[j].a,c[j].b})if(h>=n&&uses[h]==1)hs.insert(h-n);
   for(int h:hs)for(int a=0;a<n+h;a++)for(int b=a;b<n+h;b++)for(int oi=0;oi<2;oi++){
    auto hv=comb(oi,vals[a],vals[b]);
    for(int cc=0;cc<n+j;cc++)if(cc!=n+h)for(int oo=0;oo<2;oo++)if(ok(comb(oo,hv,vals[cc]))){auto d=c;d[h]={oi,a,b};d[j]={oo,n+h,cc};tested++;if(eval(d,in).back()!=target)return 7;emit(d);std::cerr<<"FOUND double repair batch="<<batches<<" parent="<<j<<" inner="<<h<<'\n';return 0;}
   }
   if(hs.size()==2){
    int h=*hs.begin(),k=*hs.rbegin();
    struct Expr {int op,a,b;V v;};
    for(int oo=0;oo<2;oo++){
     auto allowed=[&](V v){return oo?!((v[0]&care[0]&~target[0])|(v[1]&care[1]&~target[1])):!((~v[0]&care[0]&target[0])|(~v[1]&care[1]&target[1]));};
     std::vector<Expr> es,fs;
     for(int a=0;a<n+h;a++)for(int b=a;b<n+h;b++)for(int op=0;op<2;op++){auto v=comb(op,vals[a],vals[b]);if(allowed(v))es.push_back({op,a,b,v});}
     for(int a=0;a<n+k;a++)if(a!=n+h)for(int b=a;b<n+k;b++)if(b!=n+h)for(int op=0;op<2;op++){auto v=comb(op,vals[a],vals[b]);if(allowed(v))fs.push_back({op,a,b,v});}
     for(auto e:es)for(auto ff:fs)if(ok(comb(oo,e.v,ff.v))){auto d=c;d[h]={e.op,e.a,e.b};d[k]={ff.op,ff.a,ff.b};d[j]={oo,n+h,n+k};tested++;if(eval(d,in).back()!=target)return 8;emit(d);std::cerr<<"FOUND triple repair batch="<<batches<<" parent="<<j<<" inners="<<h<<","<<k<<'\n';return 0;}
    }
   }
  }
 }
 std::cerr<<"No exact repair: batches="<<batches<<" eligible_parents="<<parents<<" expressions="<<expressions<<" tested="<<tested<<'\n';return 1;
}
