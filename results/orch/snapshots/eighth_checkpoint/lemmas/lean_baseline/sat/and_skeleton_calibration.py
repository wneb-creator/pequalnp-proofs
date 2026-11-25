from pathlib import Path
from and_skeleton_sat import boundary,solve,verify


def problem(n,edges):
    positive,negative=boundary(n,edges)
    return {'inputs':n,'edges':edges,'tests':[{'mask':m,'label':1} for m in sorted(positive)]+
            [{'mask':m,'label':0} for m in sorted(negative)]}


def main():
    folder=Path('/tmp/oec/pequalnp-pilot-57/and-skeleton-small-calibration')
    single=problem(2,[(0,1)])
    one={'inputs':2,'and_gates':[{'left':[0],'right':[1]}],'output':[2]}
    assert verify(single,one,full=True)
    assert solve(single,one,folder/'single_clean',10,dirty=False,calibration=True)==10
    assert solve(single,one,folder/'single_dirty',10,dirty=True)==20
    empty={'inputs':2,'and_gates':[{'left':[],'right':[]},{'left':[0],'right':[1]}],'output':[3]}
    assert verify(single,empty,full=True)
    assert solve(single,empty,folder/'unused_false_node',10,calibration=True)==10
    matching=problem(4,[(0,1),(2,3)])
    clean={'inputs':4,'and_gates':[{'left':[0],'right':[1]},{'left':[2],'right':[3]}],'output':[4,5]}
    assert verify(matching,clean,full=True)
    assert solve(matching,clean,folder/'matching_clean',10,calibration=True)==10
    dirty={'inputs':4,'and_gates':[{'left':[0,2],'right':[1,3]},
            {'left':[0],'right':[1]},{'left':[2],'right':[3]},
            {'left':[4],'right':[5,6]}],'output':[7]}
    assert verify(matching,dirty,dirty_mask=9,full=True)
    assert solve(matching,dirty,folder/'matching_dirty',10,dirty=True)==10
    path=problem(4,[(0,1),(2,1),(2,3)])
    path_dirty={'inputs':4,'and_gates':[{'left':[0,2],'right':[1,3]},
                {'left':[1,2],'right':[4]}],'output':[5]}
    assert verify(path,path_dirty,dirty_mask=9,full=True)
    assert solve(path,path_dirty,folder/'path_dirty_minimum2',10,dirty=True)==10
    print('PASS faithfulAND-skeleton smallcases,emptyOR/unusednode,anddirty independentinput',flush=True)

if __name__=='__main__':main()
