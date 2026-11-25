#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
int pc(int x){return popcount((unsigned)x);}
struct Side {
  int eligible, opposite, poss=0;
  vector<int> neighbors, otherNeighbors;
  Side(int e,int o,const vector<int>& n,const vector<int>& on):
      eligible(e),opposite(o),neighbors(n),otherNeighbors(on) {
    for(int i=0;i<(int)n.size();++i) if(!(n[i]&~o)) poss|=1<<i;
  }
  // Return frequency by exact empty count and forced saturated mask.  The
  // threshold z is the proposed common budget for singleton-empty forks.
  map<pair<int,int>,int> count(int rem,int z) const {
    map<pair<int,int>,int> result;
    for(int p=poss;;p=(p-1)&poss) {
      int empty=pc(~eligible&~p&((1<<neighbors.size())-1));
      if(empty<=z){
        int sum=0;
        vector<int> extra;
        for(int i=0;i<(int)otherNeighbors.size();++i){
          int w=otherNeighbors[i];
          int pure=pc(p&w)+bool(w&~p)-1-((opposite>>i)&1);
          extra.push_back(max(0,pure));sum+=extra.back();
        }
        bool good=sum<=rem;int sat=0;
        for(int i=0;good&&i<(int)otherNeighbors.size();++i){
          int w=otherNeighbors[i],k=pc(w&~eligible),e=pc(w&eligible);
          int upper=((opposite>>i)&1)+rem-sum+extra[i];
          if(k+bool(e)-1>upper)good=false;
          if((opposite>>i&1)&&e>=2&&upper<=k)sat|=1<<i;
        }
        if(good)++result[{empty,sat}];
      }
      if(!p)break;
    }
    return result;
  }
};
int coverBound(int ineligible,int eligibleOther,const vector<int>& neighborhoods){
  vector<int> restrictions;
  for(int w:neighborhoods){
    int ns=w&ineligible;
    if(pc(ns)+bool(w&~ineligible)>2&&pc(ns)>=2)restrictions.push_back(ns);
  }
  int largest=0;
  for(int s=ineligible;;s=(s-1)&ineligible){
    if(pc(s)>largest && all_of(restrictions.begin(),restrictions.end(),[s](int r){return pc(r&s)<=1;}))largest=pc(s);
    if(!s)break;
  }
  return pc(ineligible)-largest;
}
int main(){
 int k,b,cap,reps;cin>>k>>b>>cap>>reps;
 vector<int> groups(b),rows(k);
 for(int j=0;j<b;++j){cin>>groups[j];for(int i=0;i<k;++i)if(groups[j]>>i&1)rows[i]|=1<<j;}
 int P=(1<<k)-1,L=(1<<b)-1;
 vector<int> neighborhood(1<<k);
 for(int p=1;p<=P;++p) neighborhood[p]=neighborhood[p&(p-1)]|rows[countr_zero((unsigned)p)];
 uint64_t all=0,clean=0,elig=0,cleanElig=0;
 for(int num=0;num<reps;++num){
  int ip,il,orbit;cin>>ip>>il>>orbit;
  int ep=P^ip,el=L^il,used=pc(ep)+pc(el);
  int mark=(coverBound(ip,el,groups)+coverBound(il,ep,rows)+1)/2;
  bool valid=false,survives=false;
  Side sp(ep,el,rows,groups),sl(el,ep,groups,rows);
  for(int z=0;z<=max(pc(ip),pc(il))&&used+mark+z<=cap;++z){
    int rem=cap-used-z;
    auto pr=sp.count(rem,z),lr=sl.count(rem,z);
    for(auto [p,pm]:pr)for(auto [l,lm]:lr){
      if(max(p.first,l.first)!=z)continue;
      uint64_t amt=(uint64_t)orbit*pm*lm;
      all+=amt;valid=true;
      // p.second is the forced saturated line set and l.second the point set.
      if(neighborhood[l.second]&p.second)continue;
      clean+=amt;survives=true;
    }
  }
  if(valid)elig+=orbit;
  if(survives)cleanElig+=orbit;
 }
 cout<<"{\"k\":"<<k<<",\"b\":"<<b<<",\"surplus_cap\":"<<cap<<",\"all_status\":"<<all<<",\"clean_status\":"<<clean<<",\"eligible_status\":"<<elig<<",\"clean_eligible_status\":"<<cleanElig<<"}\n";
}
