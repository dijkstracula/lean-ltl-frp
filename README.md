# lean-ltl-frp

A small Lean 4 library for reasoning about reactive systems: linear temporal
logic (LTL), functional reactive programming (FRP), and refinement-typed
signals that carry their own safety proofs, loosely inspired by Jane Street's
`incremental` and Jeffrey's [LTL types
FRP](https://dl.acm.org/doi/epdf/10.1145/2103776.2103783) paper. It's the
machine-checked companion to the *Reactive Programming in Lean* series:
<https://ntaylor.ca/posts/lean-ltl/>.

## Requirements

- A Lean toolchain. [`elan`](https://github.com/leanprover/elan) reads
  `lean-toolchain` and installs the pinned version (`leanprover/lean4:v4.32.1`)
  for you.

## Building

```sh
lake build
```

This builds both the `LtlFrp` library and the per-blog post `Examples`.

## Layout

```
LtlFrp/                  the library
  Trace.lean             Time, Trace, now/drop, StateProp/TraceProp
  LTL.lean               temporal operators □ ◇ ○ U, atom, until, implies
  FRP/Simple.lean        the non-dependent FRP interface — Signal AND Event and
                         their combinators: map/map2, scan, clock, merge, latch
  FRP/Verified.lean      the refinement-typed layer: RSignal, the □ // and ⦃ ⦄
                         notation, split/collect, refined map/map2/weaken, accumulate
  FRP/Hoare.lean         Hoare-style combinators: hoare_seq/if, while, Event.when
Examples/
  Ltl1.lean … Ltln.lean  one module per blog post
```

The Lean module namespace is `LtlFrp` (e.g. `import LtlFrp.FRP.Refining`), which
is independent of the package name.

## Anchors for blog listings

Definitions in `LtlFrp/` are wrapped in mdBook-style anchors:

```lean
-- ANCHOR: rsignal-split
def RSignal.split (sig : (□ β) // inv) : □ (β // inv) := ...
-- ANCHOR_END: rsignal-split
```

The blog includes these regions directly (as a submodule, via a `{% lean %}`
shortcode), so every listing on the site is exactly what compiles here.
