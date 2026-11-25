# Primary-input NOT investigation

2026-11-25T14:17:12.127366+00:00

A general cost-preserving elimination theorem remains unproved. Do not assume it.

Exhaustive C++ enumeration on four inputs supplied NOT(x0) as an additional free input, then enumerated up to six binary AND/OR gates with distinct nonconstant new wires. Comparison with positive-only enumeration found no monotone output with improved binary-gate cost. Signed states: 694,657,939; positive-only states: 76,599,433. This is computational evidence, not a Lean certificate. At five gates, counts were 14,883,469 and 2,287,777.

A safe syntactic necessary condition: if exactly one NOT is applied to primary input i and input i is never read elsewhere, every gate output is antitone in i. Petersen depends increasingly on every input, so the input must also be read positively.

The tempting strategy of replacing the NOT by one constant uniformly is false in general, even for monotone outputs: (x AND z) OR (y AND z) OR (x AND y), evaluated at z=NOT x, equals y; replacement z=0 gives x AND y, and z=1 gives x OR y.

A valid semantic identity is available: if G is monotone in its input vector and extra Boolean z, and f(x)=G(x,NOT x_i) is monotone, then f(x)=G(x,0) OR G(x[i:=0],1). This removes the negation semantically but can require duplicating gates, so it gives no cost-preserving circuit bound by itself.

Source search restricted to GitHub found no primary source resolving the exact cost-preserving claim. No external numerical figures are used above.

## Reproduction

The enumeration excludes constant gates, copies, repeated input gates, and duplicate wires; each is removable without increasing the number of binary gates for a nonconstant single output. Gate labels range over all earlier wires, so every remaining circuit in this bounded class is enumerated. This normalization argument is informal; no theorem is claimed from the search alone.

Commands (C++17): compile the program below with `g++ -O3 -std=c++17`, run with arguments `6 1` for the supplied negated input and `6 0` for positive inputs only. Compare each `result f cost` line. The program prints every discovered improving witness and final per-function costs; 99 means not found within budget.

```cpp
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

std::array<uint16_t, 16> wires;
std::array<int, 65536> best;
std::array<bool, 65536> mono;
std::array<int, 16> pa, pb, po;
uint64_t states = 0;
int bound, initial;
bool neg;
void dfs(int depth) {
  ++states;
  if (depth == bound) return;
  int top = initial + depth;
  for (int a = 0; a < top; ++a) for (int b = a+1; b < top; ++b) {
    for (int op = 0; op < 2; ++op) {
      uint16_t v = op ? wires[a] | wires[b] : wires[a] & wires[b];
      if (v == 0 || v == 65535) continue;
      if (std::find(wires.begin(), wires.begin()+top, v) != wires.begin()+top) continue;
      wires[top] = v; pa[top]=a; pb[top]=b; po[top]=op;
      if (mono[v] && depth+1 < best[v]) {
        best[v]=depth+1;
        std::cout << "best " << v << " " << depth+1 << " gates";
        for(int k=initial;k<=top;++k) std::cout<<" ("<<po[k]<<","<<pa[k]<<","<<pb[k]<<")";
        std::cout << std::endl;
      }
      dfs(depth+1);
    }
  }
}
int main(int argc,char**argv){
  bound=argc>1?std::stoi(argv[1]):5;
  neg=argc>2 && std::stoi(argv[2]);
  initial=neg?5:4;
  best.fill(99);
  for(int f=0;f<65536;++f){
    bool ok=true;
    for(int r=0;r<16;++r) for(int i=0;i<4;++i)
      if(!(r&(1<<i)) && ((f>>r)&1) && !((f>>(r|(1<<i)))&1))ok=false;
    mono[f]=ok;
  }
  for(int i=0;i<4;++i){
    uint16_t v=0;
    for(int r=0;r<16;++r) if((r>>i)&1)v|=1<<r;
    wires[i]=v; best[v]=0;
  }
  wires[4]=~wires[0];
  dfs(0);
  std::cout << "states " << states << std::endl;
  for(int f=0;f<65536;++f)if(mono[f])std::cout<<"result "<<f<<" "<<best[f]<<std::endl;
}
```
