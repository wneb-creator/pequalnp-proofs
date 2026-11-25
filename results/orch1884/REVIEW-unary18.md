# Independent review: monotone circuits with a free unary input

UTC: 2026-11-25T15:55:20.360645+00:00
Verdict: PASS for the newly checked dependency test and its unconditional eighteen-gate floor. A standalone assembly has not been checked; the exact eighteen-gate exclusion remains unproved.

Source: `results/orch1884/lemmas/Unary18Check.lean`
SHA256: `74c00733e29ca7a1706277a07a000c2b37164ae1fedf9a9a976f30d7de26eae5`
Size: 49852 bytes; 982 lines.
New extension: `results/orch1884/lemmas/Unary18Extension.lean`; SHA256 `16f233d96b3bc2b7025c335b5d0bceec931a167d0b3c7eaf6a0c4bcd98fb45c7`. Its complete text occurs unchanged in the checked test.
Prior monotone extension test: results/orch2590/lemmas/MonoExtensionCheck.lean; SHA256 `a8ca2c6b7a172a30561130537d65c4fdd25744124e4a1c6ddde46deea795c591`.

The author confirms successful Lean exit 0 for both extension tests. Both import the now checked MonoBase object. Complete log records:

[
  {
    "path": "results/orch1884/unary18-checked.stdout",
    "bytes": 3818,
    "sha256": "18fbc3dc1f354f8ef4a0d39de93239cb38168364bcd1ac8d9843c4fdc8498b23",
    "warnings": 12
  },
  {
    "path": "results/orch1884/unary18-checked.stderr",
    "bytes": 0,
    "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "warnings": 0
  },
  {
    "path": "results/orch1884/mono-extension-checked.stdout",
    "bytes": 3582,
    "sha256": "7c72280aae6541f63555745a22e7df66872621189f92e81c0e7196bc2f861a2a",
    "warnings": 11
  },
  {
    "path": "results/orch1884/mono-extension-checked.stderr",
    "bytes": 0,
    "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "warnings": 0
  }
]

## Composition and hypotheses

The prior monotone extension is the one semantically reviewed in results/orch2590/REVIEW-mono18.md; its new dependency test now compiled. The Unary18 copy changes the shared nine-variable floor into an explicit parameter and passes it through affected helper calls. Those changes do not strengthen the assumptions. The final unary_mono_size_eighteen theorem explicitly supplies the checked MonoBase.nineMonoFloor, so its public statement has no unproved certificate premise.

The arbitrary input map may omit, duplicate, or reorder inputs; no permutation assumption is added. The arbitrary unary function is exactly one of zero, one, pin 0, or negative pin 0. Constants are discarded from proper live roots. In monotone mode the free negative pin is retained as a possible input, and is not incorrectly normalized into a positive pin.

If the negative pin is absent from the extracted live root set, the prior unconditional monotone eighteen-gate floor applies. If it is present, the directional Live lemma applied to rows 128 and 640 forces the positive pin 0 to be live as well: the target increases, the negative pin decreases, and every other raw pin stays fixed. Under x0=false projection, those two distinct roots become the two constants zero and one, while the target becomes the checked nine-variable cofactor. The projected-bound mass term charges both distinct roots, giving sixteen plus two gates. This accounts for the arbitrary free unary input without charging it as a circuit gate.

The standard Circuit extraction assumes Monotone2, including AND/OR gates of fan-in at most two, and preserves its actual evaluation conventions for empty/unary gates, duplicate operands, invalid reads, and unused gates. There are no paid NOT gates in this theorem. The resulting lower bound is only 18 <= C.size; it allows equality and does not discharge L-meta-1884.

## Preservation and eventual assembly

The dependency test imports MonoBase, so it is an archive test rather than a Defs-only final submission. The actual base source hash is e1d85e65b52da547c990de4b3ac2da8fa966657990324c3ef784d1dcee2f050e; object hash fd8c245893d6eabfe9c650557a123b21ba15039252c462a78cd2e9c79dfd74dc. The prior reviewed build establishes this dependency with no new axioms. A direct full-base plus extension concatenation would slightly exceed 512 KiB, so a final single-file assembly needs pruning and a fresh build rather than assuming this test alone satisfies that format limit.

No sorry, axiom, native_decide, forbidden namespace substring, double quote, attribute, unsafe/meta declaration, or disallowed option occurs in the reviewed extension sources. No credential material was observed. The reviewer did not author the new unary extension; the reused directional lemma was independently reviewed earlier.
