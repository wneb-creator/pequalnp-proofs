#define ORBIT_NO_MAIN
#include "orbits.cpp"
int main(int argc,char**argv){
 if(argc<2)return 2;
 U total=0;for(int p=0;p<7;p++)for(int q=p+1;q<7;q++)pairs2.push_back({p,q});
 for(int s=0;s<128;s++){U mask=0;for(int k=0;k<21;k++){auto[p,q]=pairs2[k];if(!(s>>p&1)&&!(s>>q&1))mask|=1U<<k;}kept[s]=mask;offset[s]=total;total+=1U<<__builtin_popcount(mask);}
 for(int t=0;t<6;t++){
  swaps[t][0]={t,t+1};int j=1;
  for(int v=0;v<7;v++)if(v!=t&&v!=t+1){pair<int,int> p={min(t,v),max(t,v)},q={min(t+1,v),max(t+1,v)};int r=find(pairs2.begin(),pairs2.end(),p)-pairs2.begin();int z=find(pairs2.begin(),pairs2.end(),q)-pairs2.begin();swaps[t][j++]={7+r,7+z};}
 }
 ifstream in(argv[1]);vector<pair<U,int>> reps;string line;
 while(getline(in,line)){istringstream row(line);U rep;int c;if(!(row>>rep>>c)||c<0||c>14){cerr<<"BAD CERTIFICATE\n";return 3;}U forced=((1U<<21)-1)^kept[rep&127];if(rep>=(1U<<28)||((rep>>7)&forced)!=forced){cerr<<"BAD SIGNATURE\n";return 3;}reps.push_back({rep,c});}
 cost.assign(total,255);array<vector<U>,15> levels;size_t covered=0;
 auto start=chrono::steady_clock::now();
 for(auto[raw,c]:reps){
  if(cost[ix(raw)]!=255){cerr<<"DUPLICATE ORBIT\n";return 4;}
  vector<U> queue={raw};cost[ix(raw)]=c;
  for(size_t j=0;j<queue.size();j++)for(int t=0;t<6;t++){
   U r=perm(queue[j],t);size_t k=ix(r);
   if(cost[k]==255){cost[k]=c;queue.push_back(r);}
   else if(cost[k]!=c){cerr<<"CONFLICTING ORBIT\n";return 5;}
  }
  covered+=queue.size();levels[c].insert(levels[c].end(),queue.begin(),queue.end());
 }
 if(covered!=total){cerr<<"INCOMPLETE COVER "<<covered<<"/"<<total<<"\n";return 6;}
 for(int v=0;v<7;v++){
  U raw=1U<<v;for(int k=0;k<21;k++)if(pairs2[k].first==v||pairs2[k].second==v)raw|=1U<<(k+7);
  if(cost[ix(raw)]!=0){cerr<<"BAD INPUT COST\n";return 7;}
 }
 if(cost[ix(0)]||cost[ix((1U<<28)-1)]){cerr<<"BAD CONSTANT COST\n";return 8;}
 size_t checks=0;
 for(auto[a,i]:reps)if(i<=6)for(int j=i;i+j+1<=13;j++)for(U b:levels[j]){
  if(cost[ix(a&b)]>i+j+1||cost[ix(a|b)]>i+j+1){cerr<<"BAD SUBADDITIVITY "<<a<<" "<<b<<"\n";return 9;}checks+=2;
 }
 U tgt=0;vector<pair<int,int>> E={{0,2},{1,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{2,6},{3,6},{5,6}};
 for(auto e:E){int k=find(pairs2.begin(),pairs2.end(),e)-pairs2.begin();tgt|=1U<<(k+7);}
 if(cost[ix(tgt)]!=14){cerr<<"TARGET POTENTIAL BELOW14\n";return 10;}
 cout<<"CERTIFICATE ACCEPTED: "<<reps.size()<<" orbits cover "<<covered<<" states; "<<checks<<" normalized binary checks; target potential "<<int(cost[ix(tgt)])<<"; elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"s\n";
}
