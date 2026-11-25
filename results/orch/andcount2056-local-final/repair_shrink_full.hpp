constexpr int MAXWORDS=12;using RV=std::array<U,MAXWORDS>;
long long repairCalls=0,repairExpressions=0;
RV rcomb(int op,const RV&a,const RV&b){RV out{};for(int k=0;k<words;k++)out[k]=op?(a[k]|b[k]):(a[k]&b[k]);return out;}
bool shrinkExact(Net&c){
 repairCalls++;eval(c);if(lastRaw!=0)return false;if(words>MAXWORDS)return false;int initialSize=activeCount(c);auto live=activeMask(c);
 std::array<RV,WIRES> vals{};for(int i=0;i<WIRES;i++)for(int k=0;k<words;k++)vals[i][k]=val[i*words+k];
 RV goal{},mask{};for(int k=0;k<words;k++){goal[k]=target[k];mask[k]=masks[k];}
 std::array<int,WIRES>uses{};for(auto g:c){uses[g.a]++;uses[g.b]++;}
 auto accept=[&](Net d){if(activeCount(d)>=initialSize)return false;eval(d);if(lastRaw==0){c=d;return true;}std::cerr<<"ERROR repair care contract failed"<<std::endl;std::abort();return false;};
 for(int j=0;j<GATES;j++){
  if(!live[j])continue;
  std::array<RV,2>outs;
  for(int b=0;b<2;b++){auto v=vals;v[INPUTS+j]=b?mask:RV{};for(int k=j+1;k<GATES;k++)v[INPUTS+k]=rcomb(c[k].op,v[c[k].a],v[c[k].b]);outs[b]=v.back();}
  RV care{};for(int k=0;k<words;k++)care[k]=outs[0][k]^outs[1][k];
  bool impossible=false;for(int k=0;k<words;k++)if((outs[0][k]^goal[k])&~care[k]&mask[k]){impossible=true;break;}if(impossible)continue;
  auto combineOK=[&](int op,const RV&a,const RV&b){repairExpressions++;for(int k=0;k<words;k++)if(((op?(a[k]|b[k]):(a[k]&b[k]))^goal[k])&care[k])return false;return true;};
  for(int a=0;a<INPUTS+j;a++)for(int b=a;b<INPUTS+j;b++)for(int op=0;op<2;op++)if(combineOK(op,vals[a],vals[b])){auto d=c;d[j]={op,a,b};if(accept(d))return true;}
  std::vector<int>hs;for(int h:{c[j].a,c[j].b})if(h>=INPUTS&&uses[h]==1)hs.push_back(h-INPUTS);
  std::sort(hs.begin(),hs.end());hs.erase(std::unique(hs.begin(),hs.end()),hs.end());
  for(int h:hs)for(int a=0;a<INPUTS+h;a++)for(int b=a;b<INPUTS+h;b++)for(int oi=0;oi<2;oi++){
   auto hv=rcomb(oi,vals[a],vals[b]);
   for(int cc=0;cc<INPUTS+j;cc++)if(cc!=INPUTS+h)for(int oo=0;oo<2;oo++)if(combineOK(oo,hv,vals[cc])){auto d=c;d[h]={oi,a,b};d[j]={oo,INPUTS+h,cc};if(accept(d))return true;}
  }
  if(hs.size()==2){
   int h=hs[0],k=hs[1];struct Expr{int op,a,b;RV v;};
   for(int oo=0;oo<2;oo++){
    auto allowed=[&](const RV&v){for(int k=0;k<words;k++)if(oo?(v[k]&care[k]&~goal[k]):(~v[k]&care[k]&goal[k]))return false;return true;};
    std::vector<Expr>es,fs;
    for(int a=0;a<INPUTS+h;a++)for(int b=a;b<INPUTS+h;b++)for(int op=0;op<2;op++){auto v=rcomb(op,vals[a],vals[b]);if(allowed(v))es.push_back({op,a,b,v});}
    for(int a=0;a<INPUTS+k;a++)if(a!=INPUTS+h)for(int b=a;b<INPUTS+k;b++)if(b!=INPUTS+h)for(int op=0;op<2;op++){auto v=rcomb(op,vals[a],vals[b]);if(allowed(v))fs.push_back({op,a,b,v});}
    for(const auto&e:es)for(const auto&f:fs)if(combineOK(oo,e.v,f.v)){auto d=c;d[h]={e.op,e.a,e.b};d[k]={f.op,f.a,f.b};d[j]={oo,INPUTS+h,INPUTS+k};if(accept(d))return true;}
   }
  }
 }
 eval(c);return false;
}
