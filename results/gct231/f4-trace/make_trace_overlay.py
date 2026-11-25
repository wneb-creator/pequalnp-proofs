"""Build an isolated, auditable row-trace overlay; never modify upstream files."""
from pathlib import Path
import hashlib
import shutil

base = Path(__file__).parent
src = base / 'openf4'
dst = base / 'trace-openf4'
dst.mkdir(exist_ok=True)
shutil.copytree(src / 'openf4', dst / 'openf4', dirs_exist_ok=True)
for name in ('openf4.h', 'config.h', 'COPYING'):
    shutil.copy2(src / name, dst / name)

def replace_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)

matrix = dst / 'openf4/src/matrix.inl'
text = matrix.read_text()
for signature, hook in (
    ('Matrix<Element>::multRow(Element * row, Element const & element, int start, int end)',
     'F4Trace::scale(row, element);'),
    ('Matrix<Element>::addMultRow(Element * row1, Element * row2, Element element, int start, int end)',
     'F4Trace::add(row1, row2, element);'),
):
    text = replace_once(text, signature + '\n    {', signature + '\n    {\n        ' + hook)
matrix.write_text(text)

ideal = dst / 'openf4/src/ideal.inl'
text = ideal.read_text()
text = replace_once(text,
    'while ( (itcp1 != 0) && (itcp1->_cp.getDegree()==d))',
    'while ( (itcp1 != 0) && (itcp1->_cp.getDegree()==d) && stat._nbCpDeg < F4Trace::batchLimit)')
text = replace_once(text, '        endCol[nbPiv - 1] = ib;\n', '''        endCol[nbPiv - 1] = ib;
        for (int traceRow = 0; traceRow < height; ++traceRow)
        {
            Polynomial<Element> tracePoly;
            NodeList<Element> * tracePos = tracePoly.getPolynomialBegin();
            for (int traceCol = 0; traceCol < width; ++traceCol)
                if (!mat.getRow(traceRow)[tau[traceCol]].isZero())
                    tracePos = tracePoly.emplaceAfter(tracePos,
                        mat.getRow(traceRow)[tau[traceCol]], tabMon[traceCol]);
            F4Trace::input(mat.getRow(traceRow), tracePoly);
        }
''')
text = replace_once(text, '        return res;\n    }\n    \n    template <typename Element>\n    void\n    Ideal<Element>::buildPolynomial',
'''        F4Trace::output(row, res);
        return res;
    }
    
    template <typename Element>
    void
    Ideal<Element>::buildPolynomial''')
text = replace_once(text, '        res.deleteAfter(pos);\n', '        res.deleteAfter(pos);\n        F4Trace::output(row, res);\n')
text = replace_once(text, '                polyOne.emplaceAfter(polyOne.getPolynomialBegin(), one, 0);\n',
                    '                polyOne.emplaceAfter(polyOne.getPolynomialBegin(), one, 0);\n                F4Trace::output(matrix.getRow(i), polyOne);\n')
ideal.write_text(text)

adapter = (base / 'openf4_qq.cpp').read_text()
trace = r'''
#include <unordered_map>
#include <sstream>
namespace F4Trace {
std::ofstream log;
std::unordered_map<const void*, unsigned long> current;
unsigned long next = 0;
int batchLimit = 32;
template<class P> void input(const void* row, const P& polynomial) {
    auto id = ++next; current[row] = id;
    log << "I\t" << id << "\t" << polynomial << '\n';
}
template<class P> void output(const void* row, const P& polynomial) {
    log << "O\t" << current.at(row) << "\t" << polynomial << '\n';
    log.flush();
}
template<class E> void scale(const void* row, const E& scalar) {
    if (scalar.isOne()) return;
    auto old = current.at(row), id = ++next; current[row] = id;
    log << "S\t" << id << "\t" << old << "\t" << scalar << '\n';
}
template<class E> void add(const void* target, const void* source, const E& scalar) {
    if (scalar.isZero()) return;
    auto left = current.at(target), right = current.at(source), id = ++next;
    current[target] = id;
    log << "A\t" << id << "\t" << left << "\t" << right << "\t" << scalar << '\n';
}
}
'''
adapter = replace_once(adapter, '#include <openf4.h>', trace + '\n#include <openf4.h>')
adapter = adapter.replace('argc!=2', '(argc!=3 && argc!=4)')
adapter = replace_once(adapter, 'Usage: openf4_qq INPUT', 'Usage: openf4_qq_trace INPUT TRACE [BATCH_LIMIT]')
adapter = replace_once(adapter, ' std::ifstream in(argv[1]);', ''' if(argc==4)F4Trace::batchLimit=std::stoi(argv[3]);
 if(F4Trace::batchLimit<1 || F4Trace::batchLimit>1024)return 5;
 F4Trace::log.open(argv[2]);
 if(!F4Trace::log)return 4;
 std::ifstream in(argv[1]);''')
adapter = replace_once(adapter, ' F4::Ideal<F4::ElementRational> ideal(polys,n);ideal.f4();',
''' F4::Ideal<F4::ElementRational> ideal(polys,n);
 for(int i=0;i<m;i++)F4Trace::log << "G\\t" << i << "\\t" << polys[i] << '\\n';
 ideal.f4();
 F4Trace::log.flush();''')
(base / 'openf4_qq_trace.cpp').write_text(adapter)
for path in (matrix, ideal, base / 'openf4_qq_trace.cpp'):
    print(hashlib.sha256(path.read_bytes()).hexdigest(), path)
