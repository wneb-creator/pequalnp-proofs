// Rebuild the reachable DAG with dead, backward-reading slots inserted earlier.
// The output remains the final gate and every reachable gate keeps its function.
Net scatterSpareSlots(const Net& c, std::mt19937& rng) {
  auto gs=compact(c);
  int spare=GATES-static_cast<int>(gs.size());
  if(spare<=0)return c;
  std::vector<int> before(gs.size());
  for(int k=0;k<spare;++k)++before[rng()%gs.size()];
  std::array<int,WIRES> mp{};
  std::iota(mp.begin(),mp.begin()+INPUTS,0);
  std::vector<Gate> rebuilt;
  for(int j=0;j<static_cast<int>(gs.size());++j){
    for(int k=0;k<before[j];++k){
      int bound=INPUTS+rebuilt.size();
      rebuilt.push_back({static_cast<int>(rng()%2),static_cast<int>(rng()%bound),static_cast<int>(rng()%bound)});
    }
    auto g=gs[j];
    mp[INPUTS+j]=INPUTS+rebuilt.size();
    rebuilt.push_back({g.op,mp[g.a],mp[g.b]});
  }
  if(rebuilt.size()!=GATES)std::abort();
  Net out;
  std::copy(rebuilt.begin(),rebuilt.end(),out.begin());
  if(!valid(out) || compact(out)!=gs)std::abort();
  return out;
}
