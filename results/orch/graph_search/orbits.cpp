#define main previous_dp_main
#include "full_formula.cpp"
#undef main
U expand(U a,U mask){
#if defined(__BMI2__)
 return _pdep_u32(a,mask);
#else
 U r=0,b=1;while(mask){U k=mask&-mask;if(a&b)r|=k;b<<=1;mask^=k;}return r;
#endif
}
vector<pair<int,int>> pairs2;
array<array<pair<int,int>,6>,6> swaps;
U perm(U x,int t){for(auto [a,b]:swaps[t]){U d=((x>>a)^(x>>b))&1;x^=(d<<a)|(d<<b);}return x;}
string feature(U x,int mode){
 U s=x&127;vector<int> vertices;for(int v=0;v<7;v++)if(!(s>>v&1))vertices.push_back(v);
 int adj[7][7]={};for(int k=0;k<21;k++)if(x>>(k+7)&1){auto[a,b]=pairs2[k];if(!(s>>a&1)&&!(s>>b&1))adj[a][b]=adj[b][a]=1;}
 int deg[7]={},tri[7]={};
 for(int a:vertices)for(int b:vertices)deg[a]+=adj[a][b];
 for(int a:vertices)for(int b:vertices)for(int c:vertices)tri[a]+=adj[a][b]*adj[a][c]*adj[b][c];
 vector<vector<int>> rows;
 for(int a:vertices){vector<int> r={deg[a]};if(mode>=1)r.push_back(tri[a]);if(mode>=2){vector<int>d;for(int b:vertices)if(adj[a][b])d.push_back(deg[b]);sort(d.begin(),d.end());r.insert(r.end(),d.begin(),d.end());}rows.push_back(r);}
 sort(rows.begin(),rows.end());ostringstream out;out<<vertices.size()<<":";
 for(auto&r:rows){for(auto a:r)out<<a<<",";out<<";";}
 return out.str();
}
#ifndef ORBIT_NO_MAIN
int main(int argc,char**argv){
 int c,i;size_t a;U total=0;
 for(int p=0;p<7;p++)for(int q=p+1;q<7;q++)pairs2.push_back({p,q});
 for(int s=0;s<128;s++){U mask=0;for(int k=0;k<21;k++){auto[p,q]=pairs2[k];if(!(s>>p&1)&&!(s>>q&1))mask|=1U<<k;}kept[s]=mask;offset[s]=total;total+=1U<<__builtin_popcount(mask);}
 if(argc<2||!load(argv[1],c,i,a))return 2;
 for(int t=0;t<6;t++){
  swaps[t][0]={t,t+1};int j=1;
  for(int v=0;v<7;v++)if(v!=t&&v!=t+1){pair<int,int> p={min(t,v),max(t,v)},q={min(t+1,v),max(t+1,v)};int r=find(pairs2.begin(),pairs2.end(),p)-pairs2.begin();int z=find(pairs2.begin(),pairs2.end(),q)-pairs2.begin();swaps[t][j++]={7+r,7+z};}
 }
 vector<bool> visited(total);array<int,15> counts{};vector<pair<U,int>> reps;
 for(int s=0;s<128;s++)for(U ed=0;ed<(1U<<__builtin_popcount(kept[s]));ed++){
  U raw=s|((((1U<<21)-1)^kept[s]|expand(ed,kept[s]))<<7);
  size_t z=ix(raw);if(visited[z])continue;
  int co=min(int(cost[z]),14);vector<U> queue={raw};visited[z]=true;U repr=raw;
  for(size_t j=0;j<queue.size();j++){
   U q=queue[j];repr=min(repr,q);
   for(int t=0;t<6;t++){U r=perm(q,t);size_t k=ix(r);if(min(int(cost[k]),14)!=co){cerr<<"BAD COST ORBIT "<<q<<" "<<r<<" "<<t<<" "<<co<<" "<<int(cost[k])<<"\n";return 3;}if(!visited[k]){visited[k]=true;queue.push_back(r);}}
  }
  counts[co]++;reps.push_back({repr,co});
 }
 cout<<"Orbits "<<reps.size()<<endl;for(int c=0;c<15;c++)cout<<c<<" "<<counts[c]<<endl;
 for(int mode=0;mode<3;mode++){
  map<string,set<int>> grouped;for(auto[rep,co]:reps)grouped[feature(rep,mode)].insert(co);
  int bad=0;for(auto&[feat,cs]:grouped)bad+=cs.size()>1;
  cout<<"feature "<<mode<<" groups "<<grouped.size()<<" costconflicts "<<bad<<endl;
 }
 if(argc>2){ofstream out(argv[2]);for(auto[rep,co]:reps)out<<rep<<" "<<co<<" "<<feature(rep,2)<<"\n";}
}
#endif
