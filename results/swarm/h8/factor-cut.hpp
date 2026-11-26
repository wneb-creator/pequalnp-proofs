#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <utility>
#include <vector>

// Search pruning only.  A positive result still needs the corresponding
// Lean oneShare, hornRule, and parityRule proof replay.
namespace H8Factor {

inline constexpr std::array<int,12> positives =
  {3,6,12,17,24,33,66,132,160,264,288,320};
inline constexpr std::array<int,12> negatives =
  {42,50,69,104,116,138,201,208,261,276,385,402};

inline bool bit(const Word& w, int row) {
  return (w[row/64] >> (row%64)) & 1;
}

struct Clause {
  uint32_t vars;
  uint32_t forbidden;
};

// A clause excludes the one assignment whose selected bits equal forbidden.
inline bool satisfiable(const std::vector<Clause>& clauses,
                        uint32_t known, uint32_t values) {
  for (;;) {
    bool changed = false;
    for (const auto& c : clauses) {
      if ((values ^ c.forbidden) & known & c.vars) continue;
      uint32_t missing = c.vars & ~known;
      if (!missing) return false;
      if (std::has_single_bit(missing)) {
        known |= missing;
        values = (values & ~missing) | (missing & ~c.forbidden);
        changed = true;
      }
    }
    if (!changed) break;
  }
  uint32_t choices = 0;
  for (const auto& c : clauses) {
    if ((values ^ c.forbidden) & known & c.vars) continue;
    choices = c.vars & ~known;
    break;
  }
  if (!choices) return true;
  uint32_t selected = choices & (0U-choices);
  return satisfiable(clauses, known|selected, values&~selected) ||
         satisfiable(clauses, known|selected, values|selected);
}

inline bool cut(const std::vector<Word>& wires, int cap) {
  const int count = int(wires.size());
  if (cap > count || count > 31) return false;
  if (cap < count-1) return true;
  int cells[12][12];
  std::array<uint32_t,12> rowLabels{}, colLabels{};
  for (int p=0; p<12; ++p) for (int n=0; n<12; ++n) {
    uint32_t labels = 0;
    for (int i=0; i<count; ++i)
      if (bit(wires[i], positives[p]) && !bit(wires[i], negatives[n]))
        labels |= uint32_t(1)<<i;
    if (std::has_single_bit(labels)) {
      cells[p][n] = std::countr_zero(labels);
      rowLabels[p] |= labels;
      colLabels[n] |= labels;
    } else cells[p][n] = -1;
  }

  std::vector<uint32_t> adj(count,0);
  bool anyParity = false;
  for (int a=0; a<count; ++a) for (int b=a+1; b<count; ++b) {
    uint32_t both = (uint32_t(1)<<a)|(uint32_t(1)<<b);
    bool inRow = false, inCol = false;
    for (uint32_t row : rowLabels) inRow |= (row&both)==both;
    for (uint32_t col : colLabels) inCol |= (col&both)==both;
    if (inRow && inCol) {
      anyParity = true;
      if (cap == count-1) return true;
      adj[a] |= uint32_t(1)<<b;
      adj[b] |= uint32_t(1)<<a;
    }
  }
  // Without a parity constraint, all wires outside satisfies every Horn rule.
  if (!anyParity) return false;

  std::vector<int> color(count,-1), component(count,-1);
  int components = 0;
  for (int start=0; start<count; ++start) {
    if (color[start]>=0) continue;
    color[start]=0; component[start]=components;
    std::vector<int> todo{start};
    while (!todo.empty()) {
      int a=todo.back(); todo.pop_back();
      uint32_t neighbors=adj[a];
      while (neighbors) {
        int b=std::countr_zero(neighbors);
        neighbors &= neighbors-1;
        if (color[b]<0) {
          color[b]=1-color[a]; component[b]=components; todo.push_back(b);
        } else if (color[b]==color[a]) return true;
      }
    }
    ++components;
  }

  std::vector<Clause> clauses;
  for (int p=0; p<12; ++p) for (int n=0; n<12; ++n) {
    int c=cells[p][n];
    if (c<0) continue;
    uint32_t aa=rowLabels[p];
    while (aa) {
      int a=std::countr_zero(aa); aa &= aa-1;
      uint32_t bb=colLabels[n];
      while (bb) {
        int b=std::countr_zero(bb); bb &= bb-1;
        if (c==a || c==b) continue;
        // Horn clause: not(inner[a] && inner[b] && not inner[c]).
        std::array<int,3> variables{a,b,c};
        std::array<int,3> forbiddenValues{1,1,0};
        Clause clause{0,0}; bool vacuous=false;
        for (int j=0;j<3;++j) {
          int v=variables[j]; uint32_t coordinate=uint32_t(1)<<component[v];
          bool forbidden=forbiddenValues[j]^color[v];
          if ((clause.vars&coordinate) && bool(clause.forbidden&coordinate)!=forbidden) {
            vacuous=true; break;
          }
          clause.vars |= coordinate;
          if (forbidden) clause.forbidden |= coordinate;
        }
        if (!vacuous) clauses.push_back(clause);
      }
    }
  }
  std::sort(clauses.begin(),clauses.end(),[](Clause a, Clause b) {
    return std::pair(a.vars,a.forbidden)<std::pair(b.vars,b.forbidden);
  });
  clauses.erase(std::unique(clauses.begin(),clauses.end(),[](Clause a, Clause b) {
    return a.vars==b.vars && a.forbidden==b.forbidden;
  }),clauses.end());
  return !satisfiable(clauses,0,0);
}

} // namespace H8Factor
