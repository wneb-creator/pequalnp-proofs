#pragma once

struct ParentProfiles {
 std::array<uint32_t,1024> profiles;
 int width=0;
 struct PairResult { uint16_t rejected=0; bool ready=false; std::array<std::pair<int,int>,16> witness; };
 std::array<PairResult,210> pairs;
 static uint16_t pairRejected(unsigned a,unsigned b) {
  uint16_t result=0;
  for(unsigned op=0;op<4;op++) {
   auto value=[&](unsigned p){bool x=p&1,y=p&2;return op==0?x&&y:op==1?x||y:op==2?x&&!y:!x&&y;};
   if(value(a)!=value(b))continue;
   for(unsigned keeps=0;keeps<4;keeps++)if(!((a^b)&keeps))result|=1U<<(op*4+keeps);
  }
  return result;
 }
 std::pair<int,int> build(const std::vector<int>&ws) {
  width=int(ws.size());if(width>20)throw std::runtime_error("profile width exceeds table");
  for(auto&p:pairs)p.ready=false;
  profiles.fill(0);
  for(int i=0;i<width;i++)for(int r=0;r<1024;r++)profiles[r]|=uint32_t(bit(wires[ws[i]].word,r))<<i;
  static std::array<int,1U<<20> representative;
  static std::array<uint32_t,1U<<20> stamps{};
  static uint32_t stamp=0;
  if(++stamp==0){stamps.fill(0);stamp=1;}
  for(int r=0;r<1024;r++){
   unsigned profile=profiles[r];int s=representative[profile];
   if(stamps[profile]==stamp&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
   representative[profile]=r;stamps[profile]=stamp;
  }
  return {-1,-1};
 }
 std::pair<int,int> cachedChild(uint32_t deleted,const Word&output) const {
  if(!deleted)return {-1,-1};
  uint32_t outbit=deleted&-deleted;
  static std::array<int,1U<<20> representative;
  static std::array<uint32_t,1U<<20> stamps{};
  static uint32_t stamp=0;
  if(++stamp==0){stamps.fill(0);stamp=1;}
  for(int r=0;r<1024;r++) {
   uint32_t profile=(profiles[r]&~deleted)|(uint32_t(bit(output,r))*outbit);
   int s=representative[profile];
   if(stamps[profile]==stamp&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
   representative[profile]=r;stamps[profile]=stamp;
  }
  return {-1,-1};
 }
 const PairResult& buildPair(int i,int j) {
  if(i>j)throw std::runtime_error("profile pair order");
  auto&answer=pairs[j*(j-1)/2+i];
  if(answer.ready)return answer;
  answer.ready=true;answer.rejected=0;answer.witness.fill({-1,-1});
  static const std::array<std::array<uint16_t,4>,4> rejectPair=[](){std::array<std::array<uint16_t,4>,4> a{};for(int p=0;p<4;p++)for(int q=0;q<4;q++)a[p][q]=pairRejected(p,q);return a;}();
  static const std::array<uint16_t,256> rejectCode=[&](){std::array<uint16_t,256> a{};for(unsigned code=0;code<256;code++)for(int p=0;p<4;p++)if(code>>p&1)for(int q=0;q<4;q++)if(code>>(q+4)&1)a[code]|=rejectPair[p][q];return a;}();
  static std::array<uint8_t,1U<<20> codes;
  static std::array<std::array<uint16_t,4>,1U<<20> rows;
  static std::array<uint32_t,1U<<20> stamps{};
  static uint32_t stamp=0;
  if(++stamp==0){stamps.fill(0);stamp=1;}
  uint32_t deleted=(1U<<i)|(1U<<j);
  for(int r=0;r<1024;r++) {
   uint32_t profile=profiles[r],group=profile&~deleted;
   unsigned pattern=((profile>>i)&1)|(((profile>>j)&1)<<1);
   bool value=bit(target,r);
   if(stamps[group]!=stamp){stamps[group]=stamp;codes[group]=0;}
   unsigned oldcode=codes[group];
   unsigned code=oldcode|(1U<<(pattern+4*value));
   uint16_t newly=rejectCode[code]&~answer.rejected;
   for(uint16_t bits=newly;bits;bits&=bits-1) {
    int flag=std::countr_zero(bits),s=-1;
    for(int q=0;q<4;q++)if((oldcode>>(q+4*!value)&1)&&(rejectPair[pattern][q]>>flag&1))s=std::max(s,int(rows[group][q]));
    if(s<0)throw std::runtime_error("missing collision witness");
    answer.witness[flag]=value?std::pair(r,s):std::pair(s,r);
   }
   answer.rejected|=newly;codes[group]=code;rows[group][pattern]=r;
   if(answer.rejected==0x7777)break;
  }
  return answer;
 }
 std::pair<int,int> pairedChild(int i,int j,int op,int keeps) {
  if(keeps==3)return {-1,-1};
  return buildPair(i,j).witness[op*4+keeps];
 }
};
