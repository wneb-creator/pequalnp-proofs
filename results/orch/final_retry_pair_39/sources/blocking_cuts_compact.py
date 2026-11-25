"""Equivalent Tseitin compression of repeated positive reader-disjunctions."""
from blocking_cuts import add_blocking


class ReaderDisjunctions:
    def __init__(self,cnf):
        self.cnf=cnf
        self.cache={}
        self.original_positive_literals=0
        self.pattern_clauses=0

    @property
    def clauses(self):
        return self.cnf.clauses

    def add(self,*lits):
        positive=tuple(v for v in lits if v>0)
        negative=tuple(v for v in lits if v<0)
        assert len(positive)+len(negative)==len(lits)
        self.original_positive_literals+=len(positive)
        self.pattern_clauses+=1
        if len(positive)<2:
            self.cnf.add(*lits)
            return
        if positive not in self.cache:
            z=self.cnf.var()
            self.cache[positive]=z
            # z iff OR(positive), a definitional extension with both directions.
            self.cnf.add(-z,*positive)
            for v in positive:self.cnf.add(-v,z)
        self.cnf.add(*negative,self.cache[positive])


def add_blocking_compact(cnf,schema,prefix):
    proxy=ReaderDisjunctions(cnf)
    stats=add_blocking(proxy,schema,prefix)
    stats.update({'reader_disjunction_flags':len(proxy.cache),
                  'pattern_clauses':proxy.pattern_clauses,
                  'original_positive_literal_occurrences':proxy.original_positive_literals})
    return stats
