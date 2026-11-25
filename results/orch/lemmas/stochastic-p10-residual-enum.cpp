#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
#include <chrono>

int main(int argc, char** argv) {
  if (argc != 3) return 2;
  const int units = std::stoi(argv[1]);
  if (units != 2 && units != 3) return 2;
  const int n = 1 << units;
  const int nb[4][3] = {{0,1,3},{0,2,6},{1,5,6},{0,4,5}};
  bool adj[4][7] = {};
  for (int i=0;i<4;i++) for(int k=0;k<3;k++) adj[i][nb[i][k]]=true;
  int card[8] = {};
  bool sub[8][8] = {};
  for(int a=0;a<n;a++) {
    for(int j=0;j<units;j++) card[a] += (a>>j)&1;
    for(int b=0;b<n;b++) sub[a][b] = a != 0 && (a & b) == a;
  }
  const auto start=std::chrono::steady_clock::now();
  std::uint64_t total=1;
  for(int t=0;t<7;t++) total*=n;
  std::vector<std::array<int,7>> survivors;
  std::uint64_t first_failure[8]={};
  for(std::uint64_t code=0;code<total;code++) {
    std::uint64_t rest=code;
    std::array<int,7> r;
    for(int t=0;t<7;t++) {r[t]=rest%n;rest/=n;}
    bool ok=true;
    for(int t=0;t<7;t++) {
      int forced=(t==0?0:1);
      for(int i=0;i<4;i++)
        forced += adj[i][t] || sub[r[nb[i][0]]][r[t]] ||
                  sub[r[nb[i][1]]][r[t]] || sub[r[nb[i][2]]][r[t]];
      if(forced>2+card[r[t]]) {first_failure[t]++;ok=false;break;}
    }
    if(ok) {survivors.push_back(r); first_failure[7]++;}
  }
  const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
  std::ofstream out(argv[2]);
  out << "{\n  \"units\": " << units << ",\n  \"enumerated\": " << total
      << ",\n  \"survivor_count\": " << survivors.size()
      << ",\n  \"seconds\": " << seconds << ",\n  \"first_failure_counts\": [";
  for(int t=0;t<8;t++) out<<(t?", ":"")<<first_failure[t];
  out << "],\n  \"survivors\": [\n";
  for(std::size_t j=0;j<survivors.size();j++) {
    out << (j?",\n":"") << "    [";
    for(int t=0;t<7;t++) out << (t?", ":"") << survivors[j][t];
    out << "]";
  }
  out << "\n  ]\n}\n";
  std::cout << "units="<<units<<" enumerated="<<total<<" survivors="<<survivors.size()<<" seconds="<<seconds<<"\n";
}
