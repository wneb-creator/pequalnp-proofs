#pragma once
struct Ends { int lo,hi; };
std::vector<Ends> ends;
void makeEnds(){
  for(const auto&p:poolData){
    int lo=1023,hi=0,count=0;
    for(int r=0;r<1024;r++)if(bit(p.domain,r)){lo&=r;hi|=r;count++;}
    if(!count||!bit(p.domain,lo)||!bit(p.domain,hi))throw std::runtime_error("domain endpoints absent");
    for(int r=0;r<1024;r++)if(bit(p.domain,r)!=((r&lo)==lo&&(r&~hi)==0))throw std::runtime_error("not subcube");
    ends.push_back({lo,hi});
  }
}

struct CompactSpec{int pool,paid,constants;uint32_t unavailable,constantmask,selected;};
struct CompactResult{size_t depth;std::vector<Word> projected;std::vector<CompactSpec> specs;};
void compactSpecs(const std::vector<int>&ws,const std::vector<Step>&prefix,bool allPaid,int cap,CompactResult& out){
  static_assert(!signedMode,"compact prototype currently uses monotone paid gates");
  out.specs.clear();out.depth=allPaid?prefix.size():std::min<size_t>(1,prefix.size());
  const size_t depth=out.depth;
  if(depth>31||ws.size()>31)throw std::runtime_error("bitmask width");
  out.projected.resize(poolData.size()*depth);
  struct Bank{uint32_t selected,unavailable;};
  std::vector<Bank> banks; banks.reserve(1U<<std::min<size_t>(depth,12));
  for(size_t pi=0;pi<poolData.size();pi++){
    const auto&p=poolData[pi];auto e=ends[pi];
    uint32_t cm=0,ones=0;
    for(size_t i=0;i<ws.size();i++){
      const auto&w=wires[ws[i]].word;
      if(bit(w,e.lo)){cm|=1U<<i;ones|=1U<<i;}
      else if(!bit(w,e.hi))cm|=1U<<i;
    }
    int maxPaid=p.bound+std::popcount(cm)-(cap-1);
    if(maxPaid<0)continue;
    Word*zs=depth?out.projected.data()+pi*depth:nullptr;
    std::array<Word,32> as,bs,masked;
    std::array<bool,32> afree,bfree,zfree;
    std::array<uint32_t,32> asupply{},bsupply{},zsupply{},liveCover{};
    for(size_t si=0;si<depth;si++){
      const auto&s=prefix[si];
      as[si]=band(wires[s.a].word,p.domain);bs[si]=band(wires[s.b].word,p.domain);
      zs[si]=binary(s.op,as[si],bs[si]);
      afree[si]=contains(p.wires,as[si]);bfree[si]=contains(p.wires,bs[si]);zfree[si]=contains(p.wires,zs[si]);
      for(size_t j=0;j<si;j++){
        if(zs[j]==as[si])asupply[si]|=1U<<j;
        if(zs[j]==bs[si])bsupply[si]|=1U<<j;
        if(zs[j]==zs[si])zsupply[si]|=1U<<j;
      }
    }
    uint32_t initialUn=0;
    for(size_t i=0;i<ws.size();i++){
      masked[i]=(cm>>i&1)?((ones>>i&1)?p.domain:zero):band(wires[ws[i]].word,p.domain);
      if(!contains(p.wires,masked[i]))initialUn|=1U<<i;
      for(size_t si=0;si<depth;si++)if(masked[i]==zs[si])liveCover[si]|=1U<<i;
    }
    banks.clear();banks.push_back({0,initialUn});
    for(size_t si=0;si<depth;si++){
      if(zfree[si])continue;
      size_t sz=banks.size();
      for(size_t i=0;i<sz;i++){
        auto b=banks[i];
        if(std::popcount(b.selected)<maxPaid&&
          (afree[si]||(b.selected&asupply[si]))&&
          (bfree[si]||(b.selected&bsupply[si]))&&!(b.selected&zsupply[si]))
          banks.push_back({b.selected|(1U<<si),b.unavailable&~liveCover[si]});
      }
    }
    for(auto b:banks)if(std::popcount(b.unavailable)<=2)
      out.specs.push_back({int(pi),std::popcount(b.selected),std::popcount(cm),b.unavailable,cm,b.selected});
  }
  return;
}

