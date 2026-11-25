import counterexample_q3_incremental as inc

original_neighborhood=inc.geometry.neighborhood

def neighborhood(rng,trial,remove_count=3):
    seed,unused_free,details=original_neighborhood(rng,trial,remove_count)
    free=list(range(len(seed)))
    and_count=sum(op for op,a,b in seed)
    assert and_count==14
    details=dict(details,rewiring='all_gates_fixed_operation_pattern',and_gates=and_count,
                 or_gates=len(seed)-and_count)
    return seed,free,details

class FixedOpsEncoding(inc.Encoding):
    def __init__(self,seed,free,patterns):
        super().__init__(seed,free,patterns)
        for i in self.free:self.add(self.ops[i] if seed[i][0] else -self.ops[i])

inc.Encoding=FixedOpsEncoding
inc.geometry.neighborhood=neighborhood
if __name__=='__main__':inc.main()
