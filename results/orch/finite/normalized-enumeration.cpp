#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
#include <unordered_map>
#include <tuple>
using namespace std;
struct Gate { int op,a,b; };
int n,p,l,limit; vector<uint64_t> values; vector<unsigned> reach; vector<Gate> gates;
vector<uint64_t> targets; vector<unsigned> edgeMasks; vector<int> lower; vector<unsigned> requiredOr; unsigned seenTarget=0;
uint64_t visits=0, checked=0, servedChecks=0, minimalChecks=0; unordered_map<uint64_t,int> targetIndex; unordered_map<uint64_t,unsigned> pureOrIndex; int familyMode=0; int pruneMode=0; vector<int> matched;
int cover(unsigned E){int r=n;for(unsigned s=0;s<(1u<<n);s++){bool yes=true;for(int a=0;a<p;a++)for(int b=0;b<l;b++)if((E>>(a*l+b)&1)&&!(s>>a&1)&&!(s>>(p+b)&1))yes=false;if(yes)r=min(r,__builtin_popcount(s));}return r;}
uint64_t orTruth(unsigned S){uint64_t f=0;for(unsigned x=0;x<(1u<<n);x++)if(x&S)f|=1ull<<x;return f;}
bool starServed(unsigned E){for(int a=0;a<p;a++)for(int b=0;b<l;b++)if(E>>(a*l+b)&1){bool ok=false;for(int j=0;j<(int)gates.size();j++)if(gates[j].op==1){for(unsigned S=1;S<(1u<<l);S++)if(__builtin_popcount(S)>=2&&(S>>b&1)&&values[n+j]==orTruth(S<<p)){bool good=true;for(int c=0;c<l;c++)if((S>>c&1)&&!(E>>(a*l+c)&1))good=false;if(good)ok=true;}for(unsigned S=1;S<(1u<<p);S++)if(__builtin_popcount(S)>=2&&(S>>a&1)&&values[n+j]==orTruth(S)){bool good=true;for(int c=0;c<p;c++)if((S>>c&1)&&!(E>>(c*l+b)&1))good=false;if(good)ok=true;}}if(!ok)return false;}return true;}

struct Component { int centre; unsigned leaves, gateBits, edgeBits; };
void dumpFailure(const char* kind, int t, const vector<Component>& comps) {
  cout << kind << " n=" << n << " p=" << p << " E=" << edgeMasks[t]
       << " tau=" << cover(edgeMasks[t]) << " gates=" << gates.size()
       << " family=" << familyMode << endl;
  for (auto g : gates) cout << g.op << " " << g.a << " " << g.b << endl;
  for (auto c : comps) cout << "component " << c.centre << " leaves=" << c.leaves
                           << " gates=" << c.gateBits << " edges=" << c.edgeBits << endl;
}
void checkLedger(int t) {
  unsigned E = edgeMasks[t]; int ec = __builtin_popcount(E), tau = lower[t]-ec+1;
  vector<unsigned> neigh(n,0);
  for(int a=0;a<p;a++) for(int b=0;b<l;b++) if(E>>(a*l+b)&1) {
    neigh[a] |= 1u<<(p+b); neigh[p+b] |= 1u<<a;
  }
  vector<Component> cs; unsigned pureEdges=0;
  for(int j=0;j<(int)gates.size();j++) if(gates[j].op==1) {
    uint64_t f=values[n+j]; unsigned mask=0;
    auto pit=pureOrIndex.find(f);
    if(pit!=pureOrIndex.end() && __builtin_popcount(pit->second)>=2)
      for(int c=0;c<n;c++) if((pit->second & ~neigh[c])==0) {
        if(c<p) {for(int b=0;b<l;b++)if(pit->second>>(p+b)&1)pureEdges|=1u<<(c*l+b);}
        else {for(int a=0;a<p;a++)if(pit->second>>a&1)pureEdges|=1u<<(a*l+c-p);}
      }
    if(familyMode==0) {
      auto it=pureOrIndex.find(f); if(it==pureOrIndex.end()) continue; mask=it->second;
    } else for(int v=0;v<n;v++) if(f>>(1u<<v)&1) mask|=1u<<v;
    if(__builtin_popcount(mask)<2) continue;
    for(int c=0;c<n;c++) if((mask & ~neigh[c])==0 &&
        (familyMode==0 || !(f>>(((1u<<n)-1)^neigh[c])&1))) {
      Component z{c,mask,1u<<j,0};
      for(int k=0;k<(int)cs.size();) {
        if(cs[k].centre==c && (cs[k].leaves & z.leaves)) {
          z.leaves |= cs[k].leaves; z.gateBits |= cs[k].gateBits;
          cs.erase(cs.begin()+k); k=0;
        } else k++;
      }
      cs.push_back(z); break;
    }
  }
  unsigned allEdges=0,allGates=0; int L=0;
  for(auto &c:cs) {
    if(c.centre<p) { for(int b=0;b<l;b++) if(c.leaves>>(p+b)&1) c.edgeBits|=1u<<(c.centre*l+b); }
    else { for(int a=0;a<p;a++) if(c.leaves>>a&1) c.edgeBits|=1u<<(a*l+c.centre-p); }
    allEdges |= c.edgeBits; allGates |= c.gateBits; L += __builtin_popcount(c.leaves);
  }
  if(allEdges!=E || pureEdges!=E) return;
  servedChecks++;
  int q=cs.size(), nonStar=gates.size()-__builtin_popcount(allGates);
  if(nonStar+L+1 < q+tau+ec) {dumpFailure("REFINED_ALL_FAILURE",t,cs);exit(2);}
  bool someGood=false; bool someGoodUnrefined=false;
  for(unsigned sel=1;sel<(1u<<q);sel++) {
    unsigned se=0,sg=0;int sl=0,sq=__builtin_popcount(sel);
    for(int i=0;i<q;i++) if(sel>>i&1) {se|=cs[i].edgeBits;sg|=cs[i].gateBits;sl+=__builtin_popcount(cs[i].leaves);}
    if(se!=E)continue;
    bool minimal=true;
    for(int i=0;i<q;i++) if(sel>>i&1) {
      unsigned without=0;for(int j=0;j<q;j++) if(j!=i&&(sel>>j&1)) without|=cs[j].edgeBits;
      if(without==E) {minimal=false;break;}
    }
    if(!minimal)continue;
    minimalChecks++;
    if((int)gates.size()-__builtin_popcount(sg)+sl+1 >= sq+tau+ec) someGood=true;
    if((int)gates.size()-__builtin_popcount(sg)+1 >= sq+tau) someGoodUnrefined=true;
  }
  if(!someGood){dumpFailure("MINIMAL_EXISTENCE_FAILURE",t,cs);exit(3);}
  if(!someGoodUnrefined){dumpFailure("MINIMAL_UNREFINED_FAILURE",t,cs);exit(4);}
}

void checkNormalized(int t) {
  checked++;
  unsigned E=edgeMasks[t];uint64_t F=targets[t];int ec=__builtin_popcount(E),tau=lower[t]-ec+1;
  int J=0,O=0;
  for(int i=0;i<(int)gates.size();i++) {
    if(gates[i].op==0){J++;if(!(values[n+i]&~F))return;}else O++;
  }
  vector<unsigned> neigh(n,0);
  for(int a=0;a<p;a++)for(int b=0;b<l;b++)if(E>>(a*l+b)&1){neigh[a]|=1u<<(p+b);neigh[p+b]|=1u<<a;}
  int Apure=0,Aexpanded=0;unsigned pureCovered=0;
  for(int i=0;i<(int)gates.size();i++)if(gates[i].op==1){
    uint64_t f=values[n+i];unsigned supp=0;
    for(int v=0;v<n;v++)if(f>>(1u<<v)&1)supp|=1u<<v;
    if(__builtin_popcount(supp)<2)continue;
    for(int c=0;c<n;c++)if((supp&~neigh[c])==0 && !(f>>(((1u<<n)-1)^neigh[c])&1)){
      Aexpanded++;
      auto it=pureOrIndex.find(f);
      if(it!=pureOrIndex.end()){
        Apure++;
        if(c<p){for(int b=0;b<l;b++)if(supp>>(p+b)&1)pureCovered|=1u<<(c*l+b);}
        else{for(int a=0;a<p;a++)if(supp>>a&1)pureCovered|=1u<<(a*l+c-p);}
      }
      break;
    }
  }
  if(pureCovered!=E)return;
  servedChecks++;
  int bound=1<<(p*l);vector<pair<int,int>> pairs(bound,{-1,-1});vector<int> covers;
  for(int a=0;a<(int)values.size();a++)for(int b=a;b<(int)values.size();b++){
    uint64_t f=values[a]&values[b];if(f&~F)continue;
    unsigned S=0;
    for(int u=0;u<p;u++)for(int v=0;v<l;v++)if((E>>(u*l+v)&1) && (f>>((1u<<u)|(1u<<(p+v)))&1))S|=1u<<(u*l+v);
    if(S && pairs[S].first<0){pairs[S]={a,b};covers.push_back(S);}
  }
  vector<int> dp(bound,1000),prev(bound,-1),used(bound,-1);dp[0]=0;
  for(int S=0;S<bound;S++)if(dp[S]<1000)for(int T:covers)if(dp[S|T]>dp[S]+1){dp[S|T]=dp[S]+1;prev[S|T]=S;used[S|T]=T;}
  int U=dp[E];if(U>=1000){cout<<"INTERNAL_NO_COVER"<<endl;exit(9);}
  int A=familyMode?Aexpanded:Apure;int B=O-A;
  if(ec>A+J+U || tau>B+U){
    cout<<"NORMALIZED_FAILURE n="<<n<<" p="<<p<<" E="<<E<<" tau="<<tau<<" family="<<familyMode<<" gates="<<gates.size()<<" Apure="<<Apure<<" Aexpanded="<<Aexpanded<<" B="<<B<<" J="<<J<<" minU="<<U<<" firstSlack="<<(A+J+U-ec)<<" secondSlack="<<(B+U-tau)<<" totalSlack="<<((int)gates.size()+2*U-ec-tau)<<endl;
    for(auto g:gates)cout<<g.op<<" "<<g.a<<" "<<g.b<<endl;
    for(int S=E;S;S=prev[S])cout<<"pair "<<pairs[used[S]].first<<" "<<pairs[used[S]].second<<endl;
    exit(2);
  }
}
void dfs(){
  visits++;int k=gates.size();
  if(k)for(int t=0;t<(int)targets.size();t++)checkNormalized(t);
  if(k<limit){
    int m=values.size();
    for(int a=0;a<m;a++)for(int b=a;b<m;b++)for(int op=0;op<2;op++){
      unsigned r=op?(reach[a]|reach[b]):0;unsigned left=(1u<<p)-1,right=((1u<<l)-1)<<p;
      if((r&left)&&(r&right))continue;
      uint64_t f=op?(values[a]|values[b]):(values[a]&values[b]);
      if(pruneMode){
        bool duplicate=false;for(int j=0;j<m;j++)if(values[j]==f&&reach[j]==r){duplicate=true;break;}
        if(duplicate)continue;
        if(k>0&&a<m-1&&b<m-1&&make_tuple(op,f,r)<make_tuple(gates.back().op,values.back(),reach.back()))continue;
      }
      values.push_back(f);reach.push_back(r);gates.push_back({op,a,b});
      dfs();gates.pop_back();reach.pop_back();values.pop_back();
    }
  }
}

int main(int argc,char**argv){if(argc<4){cerr<<"usage: n p max_gates [family [pruning]]"<<endl;return 64;}n=atoi(argv[1]);p=atoi(argv[2]);l=n-p;limit=atoi(argv[3]);familyMode=argc>4?atoi(argv[4]):0;pruneMode=argc>5?atoi(argv[5]):0;if(n<2||n>6||p<1||p>=n||limit<0||limit>=32||familyMode<0||familyMode>1||pruneMode<0||pruneMode>1){cerr<<"unsupported arguments"<<endl;return 64;}for(unsigned S=1;S<(1u<<n);S++)pureOrIndex[orTruth(S)]=S;for(int i=0;i<n;i++){values.push_back(orTruth(1u<<i));reach.push_back(1u<<i);}for(unsigned E=1;E<(1u<<(p*l));E++){bool c4=false,bare=false;for(int a=0;a<p;a++)for(int b=0;b<l;b++)if(E>>(a*l+b)&1){int da=0,db=0;for(int c=0;c<l;c++)da+=E>>(a*l+c)&1;for(int c=0;c<p;c++)db+=E>>(c*l+b)&1;if(da<2&&db<2)bare=true;}for(int a=0;a<p;a++)for(int aa=a+1;aa<p;aa++)for(int b=0;b<l;b++)for(int bb=b+1;bb<l;bb++)if((E>>(a*l+b)&1)&&(E>>(aa*l+b)&1)&&(E>>(a*l+bb)&1)&&(E>>(aa*l+bb)&1))c4=true;if(c4||bare)continue;int lb=__builtin_popcount(E)+cover(E)-1;if(lb<=1)continue;uint64_t f=0;for(unsigned x=0;x<(1u<<n);x++){bool y=false;for(int a=0;a<p;a++)for(int b=0;b<l;b++)if((E>>(a*l+b)&1)&&(x>>a&1)&&(x>>(p+b)&1))y=true;if(y)f|=1ull<<x;}targetIndex[f]=targets.size();targets.push_back(f);edgeMasks.push_back(E);lower.push_back(lb);}cout<<"n="<<n<<" p="<<p<<" limit="<<limit<<" family="<<familyMode<<" pruning="<<pruneMode<<" target_count="<<targets.size()<<endl;dfs();cout<<"DONE visits="<<visits<<" graph_checks="<<checked<<" served_checks="<<servedChecks<<" unused_counter="<<minimalChecks<<" no_counterexample"<<endl;}
