// Equal-cost contextual rewrites; the caller still checks the actual gate count.
// No completeness claim: this is a search move with a full boundary-table guard.
long long neutralCalls = 0, neutralOptions = 0, neutralMoves = 0;
bool neutralCare(Net& c, std::mt19937& rng) {
  ++neutralCalls;
  eval(c);
  if (lastRaw || words > MAXWORDS) return false;
  auto live = activeMask(c);
  std::vector<int> choices;
  for (int j = 0; j < GATES; ++j) if (live[j]) choices.push_back(j);
  if (choices.empty()) return false;
  int j = choices[rng() % choices.size()];
  std::array<RV, WIRES> vals{};
  for (int i = 0; i < WIRES; ++i)
    for (int k = 0; k < words; ++k) vals[i][k] = val[i * words + k];
  RV full{};
  for (int k = 0; k < words; ++k) full[k] = masks[k];
  std::array<RV, 2> outs;
  for (int b = 0; b < 2; ++b) {
    auto v = vals;
    v[INPUTS + j] = b ? full : RV{};
    for (int h = j + 1; h < GATES; ++h)
      v[INPUTS + h] = rcomb(c[h].op, v[c[h].a], v[c[h].b]);
    outs[b] = v.back();
  }
  RV care{};
  for (int k = 0; k < words; ++k) {
    care[k] = outs[0][k] ^ outs[1][k];
    if ((outs[0][k] ^ target[k]) & ~care[k] & masks[k]) return false;
  }
  Gate old = c[j], picked = old;
  if (old.a > old.b) std::swap(old.a, old.b);
  // Half of calls require a genuinely different wire profile, so that semantic
  // aliases do not monopolize the reservoir. This is a heuristic only.
  bool requireDifferentProfile = rng() % 2;
  unsigned seen = 0;
  for (int a = 0; a < INPUTS + j; ++a)
    for (int b = a; b < INPUTS + j; ++b)
      for (int op = 0; op < 2; ++op) {
        if (Gate{op, a, b} == old) continue;
        bool ok = true, different = false;
        for (int k = 0; k < words; ++k) {
          U v = op ? vals[a][k] | vals[b][k] : vals[a][k] & vals[b][k];
          if ((v ^ target[k]) & care[k]) { ok = false; break; }
          different |= ((v ^ vals[INPUTS + j][k]) & masks[k]) != 0;
        }
        if (!ok || (requireDifferentProfile && !different)) continue;
        ++neutralOptions;
        if (rng() % ++seen == 0) picked = {op, a, b};
      }
  if (!seen) return false;
  Net next = c;
  next[j] = picked;
  if (!valid(next)) std::abort();
  eval(next);
  if (lastRaw) {
    std::cerr << "ERROR neutral care contract failed" << std::endl;
    std::abort();
  }
  c = next;
  ++neutralMoves;
  return true;
}
