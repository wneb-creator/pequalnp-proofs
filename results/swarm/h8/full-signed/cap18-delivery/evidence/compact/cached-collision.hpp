#pragma once

// A child retains all but at most two parent signals and adds one output.
// Once the parent separates opposite target values, retaining every signal
// cannot create a collision. Otherwise put the output in one deleted slot:
// this sparse profile has exactly the child's equivalence classes.
struct CachedProfiles {
 std::array<uint32_t,1024> profiles;
 static inline std::array<int,1U<<20> representative;
 static inline std::array<uint32_t,1U<<20> stamps{};
 static inline uint32_t stamp=0;
 static void nextStamp(){if(++stamp==0){stamps.fill(0);stamp=1;}}
 std::pair<int,int> build(const std::vector<int>&ws) {
  if(ws.size()>20)throw std::runtime_error("profile width exceeds table");
  profiles.fill(0);
  for(size_t i=0;i<ws.size();i++)for(int r=0;r<1024;r++)profiles[r]|=uint32_t(bit(wires[ws[i]].word,r))<<i;
  nextStamp();
  for(int r=0;r<1024;r++){
   unsigned profile=profiles[r];int s=representative[profile];
   if(stamps[profile]==stamp&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
   representative[profile]=r;stamps[profile]=stamp;
  }
  return {-1,-1};
 }
 // Requires build(parent) to have returned no collision. Deleted bits refer
 // to the parent's original order; output is the newly appended truth table.
 std::pair<int,int> child(uint32_t deleted,const Word&output) const {
  if(!deleted)return {-1,-1};
  uint32_t outbit=deleted&-deleted;
  nextStamp();
  for(int r=0;r<1024;r++) {
   uint32_t profile=(profiles[r]&~deleted)|(uint32_t(bit(output,r))*outbit);
   int s=representative[profile];
   if(stamps[profile]==stamp&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
   representative[profile]=r;stamps[profile]=stamp;
  }
  return {-1,-1};
 }
};
