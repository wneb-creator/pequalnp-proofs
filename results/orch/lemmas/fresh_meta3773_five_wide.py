"""Use indistinguishable occurrences of each feature in the read-once inner solver."""
import ctypes,functools,resource,sys
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
resource.setrlimit(resource.RLIMIT_AS,(800<<20,800<<20))
import fresh_meta3773_five_search_v2 as driver
import fresh_meta3773_extended_model as model
lib=ctypes.CDLL(str(model.job/'fresh-meta3773-readonce-wide.so'))
fn=lib.feasible_multiset
fn.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.c_uint64,ctypes.c_uint64]
fn.restype=ctypes.c_int
@functools.lru_cache(maxsize=20000)
def solve(F,p,n):
 values=(ctypes.c_uint64*len(F))(*F);ans=fn(len(F),values,p,n)
 if ans<0:return model.feasible(F,p,n)
 return bool(ans)
driver.feasible=solve
if __name__=='__main__':
 cfg,used,dup=map(int,sys.argv[1:4]);assert cfg==model.cfg;print('model',model.data['points'],'rows',model.NP,len(model.N),'group',len(driver.rpi),flush=True);print(driver.run(used,dup),flush=True)
