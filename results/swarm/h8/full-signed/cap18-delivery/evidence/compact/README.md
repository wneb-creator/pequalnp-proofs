# Compact signed search banks

This optional native-engine update combines the independently reviewed exact
collision cache with a compact representation of projection supply banks.
It preserves the original signed search's model and bounds. It is not a Lean
proof of any new lower bound.

Each pool's fixed roots are stored once. A paid bank stores only its additional
signals; every membership query uses the union of the roots and those extras.
Expanding that representation yields exactly the original ordered word vector.
The independent source review records this invariant and checks every consumer.

Validation:

* Every one of 832,145 specifications on 1,001 stratified cap-18 parents has
  identical metadata and identical expanded words.
* Stored words in that sample fall from 15,483,108 to 1,727,588. Supply-bank
  construction time falls from 1.486 to 1.130 seconds.
* The complete cap-17 run reproduces all 18 frontier files, the entire wire
  table, and the collision-pair histogram byte for byte.
* Both known 20-gate Petersen circuits pass all projection/collision checks;
  all 120 symmetry images agree on all 1024 rows.
* A whole-engine sample of 201 cap-18 parents produces the same 243,568 moves
  and 1,268 children. CPU time is 0.699 seconds for the original implementation,
  0.487 for the collision cache alone, and 0.388 for this combined update.

The sample timings are measurements from this machine and load. Full output
and error streams are included. The larger cap-18 run remains an ongoing
experiment; no cap-18 closure is claimed here.

Generate `probe-data.hpp` and `pools.bin` with the included `signed_data.py`,
then compile `signed-compact.cpp` with a C++20 compiler and the generated header
directory on its include path. Keep `cached-collision.hpp` beside the source.
The executable has the same positional arguments and checked restart format
as `signed-resume.cpp` in the earlier signed research package. Run it in a
directory containing `pools.bin`; use a different output directory for restart.

`compact-known-sanity.cpp` is a separate executable exercising the two known
circuits against this implementation. `validation.json` summarizes the exact
comparisons; `compact-review.json` is the independent source review.
