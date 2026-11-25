#include <sstream>

std::vector<Gate> read_hint(const std::string& path,std::string& last_content,
                            const std::vector<Row>& rows,int n_gates) {
  std::ifstream file(path);
  if(!file) return {};
  std::string content((std::istreambuf_iterator<char>(file)),std::istreambuf_iterator<char>());
  if(content==last_content) return {};
  last_content=content;
  std::istringstream data(content);
  int count;
  if(!(data>>count) || count!=n_gates) {
    std::cout<<"hint_rejected wrong_gate_count"<<std::endl;return {};
  }
  std::vector<Gate> gates;
  for(int i=0;i<count;++i) {
    int op,left,right;
    if(!(data>>op>>left>>right) || (op!=0 && op!=1) || left<0 || left>right || right>=14+i) {
      std::cout<<"hint_rejected invalid_gate"<<std::endl;return {};
    }
    gates.push_back({left,right,bool(op)});
  }
  std::string extra;
  if(data>>extra) {std::cout<<"hint_rejected trailing_data"<<std::endl;return {};}
  for(auto row:rows) if(row.active && evaluate(gates,row.mask)!=row.expected) {
    std::cout<<"hint_rejected active_row "<<row.mask<<std::endl;return {};
  }
  std::cout<<"hint_valid_active_rows"<<std::endl;
  return gates;
}
