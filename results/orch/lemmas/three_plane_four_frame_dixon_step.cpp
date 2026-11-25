#define main checkpoint_worker_main
#include "four_frame_macaulay_checkpoint.cpp"
#undef main
#include <limits>
using I=int64_t;
struct IntegerTerm{int column;I coefficient;};
bool solve_residual(const std::vector<I>& residual,const Field& f,const std::vector<Pivot>& pivots,const std::vector<int>& bycol,int rows,std::vector<u32>& witness){
 int cols=bycol.size();std::vector<u32> work(cols),weights(pivots.size());witness.assign(rows,0);
 for(int i=0;i<cols;i++){I value=residual[i]%(I)f.p;if(value<0)value+=(I)f.p;work[i]=(u32)value;}
 for(int col=0;col<cols;col++){u32 coefficient=work[col];if(!coefficient)continue;int pivot=bycol[col];if(pivot<0)return false;weights[pivot]=(u32)(((u64)weights[pivot]+coefficient)%f.p);for(auto term:pivots[pivot].data)work[term.index]=f.sub(work[term.index],f.mul(coefficient,term.value));}
 for(int k=(int)pivots.size()-1;k>=0;k--){u32 w=f.mul(weights[k],pivots[k].inv);witness[pivots[k].origin]=w;for(auto dep:pivots[k].deps)weights[dep.index]=f.sub(weights[dep.index],f.mul(w,dep.value));}return true;
}
int main(int argc,char**argv){
 if(argc!=9)return 2;std::string binding=std::string(argv[5])+argv[6];if(binding.size()!=128||binding.find_first_not_of("0123456789abcdef")!=std::string::npos)return 3;
 std::ifstream matrix(argv[1]);int cols,rows;matrix>>cols>>rows;u64 prime=std::stoull(argv[3]);int steps=std::stoi(argv[8]);if(!matrix||prime<3||prime>2147483647||steps<1||steps>20)return 4;
 Field f(prime);std::vector<Pivot> pivots;std::vector<int> bycol(cols,-1);int next=restore(argv[4],filehash(argv[1]),binding,prime,cols,rows,matrix,pivots,bycol);
 std::vector<bool> retained(rows);for(const auto& pivot:pivots)retained[pivot.origin]=true;
 matrix.clear();matrix.seekg(0);int c0,r0;matrix>>c0>>r0;if(c0!=cols||r0!=rows)return 5;std::vector<std::vector<IntegerTerm>> integer_rows(rows);std::vector<__int128_t> absolute_sum(cols);
 for(int row=0;row<rows;row++){int count;matrix>>count;if(!matrix||count<0||count>cols)return 6;int previous=-1;for(int k=0;k<count;k++){int column;I coefficient;matrix>>column>>coefficient;if(!matrix||column<=previous||column>=cols)return 7;previous=column;if(retained[row]){integer_rows[row].push_back({column,coefficient});absolute_sum[column]+=(coefficient<0?-(__int128_t)coefficient:(__int128_t)coefficient);}}}
 __int128_t bound128=1;for(auto a:absolute_sum)bound128=std::max(bound128,a+1);if(bound128*(__int128_t)prime+bound128>std::numeric_limits<I>::max())return 8;I bound=(I)bound128;
 std::ifstream input(argv[7]);int input_cols,input_rows;u64 iteration;input>>input_cols>>input_rows>>iteration;if(!input||input_cols!=cols||input_rows!=rows||iteration>1000000)return 9;std::vector<I> residual(cols);for(I& value:residual){input>>value;if(!input||value< -bound||value>bound)return 10;}
 std::vector<std::vector<u32>> digits;std::ofstream out(argv[2]);
 for(int step=0;step<steps;step++){
  std::vector<u32> delta;if(!solve_residual(residual,f,pivots,bycol,rows,delta)){out<<"{\"consistent\":false,\"failed_iteration\":"<<iteration+step<<"}\n";return 0;}
  for(int row=0;row<rows;row++)if(delta[row])for(auto term:integer_rows[row])residual[term.column]-=(I)delta[row]*term.coefficient;
  for(I& value:residual){if(value%(I)prime!=0)return 11;value/=(I)prime;if(value< -bound||value>bound)return 12;}
  digits.push_back(std::move(delta));
 }
 out<<"{\"consistent\":true,\"prime\":"<<prime<<",\"rank\":"<<pivots.size()<<",\"next_row\":"<<next<<",\"start_iteration\":"<<iteration<<",\"end_iteration\":"<<iteration+steps<<",\"digits\":[";
 for(int k=0;k<steps;k++){if(k)out<<",";out<<"[";for(int i=0;i<rows;i++){if(i)out<<",";out<<digits[k][i];}out<<"]";}out<<"],\"carry\":[";for(int j=0;j<cols;j++){if(j)out<<",";out<<residual[j];}out<<"]}\n";return 0;
}
