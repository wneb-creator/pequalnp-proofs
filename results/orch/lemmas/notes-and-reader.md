Positive AND reader fourth-deletion application plan (not yet implemented).

Checked reusable compiler: ReaderCharge.compile_known. It returns size bound, FanInTwo, full semantic simulation, Known constants, reference bounds, and encoding length. Copied compiler cs from ReaderDeletion; arbitrary known-constant wire set ks. Each gate is charged once when its effective input list intersects ks.

Concrete target can initially fix first input i=0; arbitrary i then follows existing automorphisms/renaming. Circuit C = NorCompression.old 0 j (pre ++ g :: post) out, g.op=AND and 0 in g.inputs. Assume g has a later consumer of index z=13+pre.length. Toolchain agent owns deriving consumer existence from unique positive reader and Petersen correctness.

After removing initial NOT0 to a free input11, front := [NOTj, AND10 11] ++ pre. Use ReaderDeletion initial encoding e0 = [F,inr4,inr0,inr1,inr6,inr7,inr3,inr5,inr2,inr8,inl true] and wC(y)=ofFn(lft y)++[!lft y0]. Copy initial simulation/bounds proof from ReaderDeletion.bound_sixteen.

1. Apply compile_known [0,10] to front. Its read count is >=1 because the explicit AND10 11 is in front. Obtain encoding e,d and full invariants; e.length=13+pre.length=z.
2. Prove cs (e,d) g=(e++[F],d): g is AND, fan-in<=2, and reads primary0. Known at0 gives e[0]=inl b; semantic simulation plus preservation of initial wire0=false proves b=false. Alternatively prove cs preserves earlier encoding entries through appends. Small gate-input length cases prove cs equality.
3. Apply compile_known [0,10] to singleton [g] to retain semantic/bounds invariants, then rewrite its output state with the exact cs equality. This step emits no gate.
4. Encoding at new index z is F by ReaderDeletion.ge. Apply compile_known [z] to post. The consumer-existence witness gives this post read count>=1. The pre charge and post charge refer to disjoint list segments, so there is no double counting even if post consumer also reads0/10.
5. Final compiled d.length <= pre.length+post.length. Original C.size=4+pre.length+post.length<=19, hence d.length<=15.
6. Construct nine-input p9 circuit from final encoding output, as in ReaderDeletion.bound_sixteen. Constant output impossible by p9 all-false/all-true; inr output gives HasCircuitSize9 p9 15, contradict accepted h15.

Result: in a size19 NOR-prefix Petersen circuit, the unique positive input0 reader cannot be AND. It must be OR. Swap/rename yields same for j. This is a genuinely additional pruning condition beyond compressed_one_not, but not yet proved.
