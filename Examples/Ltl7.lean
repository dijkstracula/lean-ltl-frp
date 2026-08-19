-- example code for lean-ltl-7

import LtlFrp

namespace Ltl7
open FRP

-- ANCHOR: rsignal-review-sig-of-refinements
-- At each time step, produce a pair: an int and a proof that `(t * 2) % 2 = 0`.
def evens: □ (Int // (· % 2 = 0)) := fun t => ⟨t * 2, by lia⟩
-- ANCHOR_END: rsignal-review-sig-of-refinements

-- ANCHOR: rsignal-review-refined-sig
-- A refined signal is a single pair: a base value-producing signal,
-- and a global safety property proof
def evens': (□ Int) // (· % 2 = 0) :=
  let vals : □ Int := fun t => t * 2 -- Note: `vals` has no refinement!
  let safety : (□ ⌜(· % 2 = 0)⌝) vals := (always_atom_iff vals).mp (by lia)
  ⟨vals, safety⟩
-- ANCHOR_END: rsignal-review-refined-sig

-- ANCHOR: rsignal-review-split-collect
example : evens = RSignal.split evens' := by
  unfold evens evens' ; simp [RSignal.split]

example : RSignal.collect evens = evens' := by
  unfold evens evens' ; simp [RSignal.collect]
-- ANCHOR_END: rsignal-review-split-collect

def incr : (i : {i : Int // i ≥ 0}) → {i : Int // i > 0} := fun i => ⟨i.val + 1, by lia⟩
#check (incr <$$> ·) -- (□ Int // ⌜· ≥ 0⌝) → (□ Int // ⌜· > 0⌝)

instance : FRP.Sig

end Ltl7
