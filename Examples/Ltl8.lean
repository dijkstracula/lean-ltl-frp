-- PARKING FILE for lean-ltl post 8 (signed systolic MAC / field-form rewrite),
-- which is not yet written. Holds the post-8-destined scratch code that ports cleanly.
--
-- Left in the scratch buffer (WIP — do not build): the two shortcut MAC bound
-- `example`s that try bare `lia` on `a * w` (nonlinear — needs the four product
-- lemmas, as in `mac_bounds` below), the signed `mul` (same nonlinear `m*n < K*K`
-- obstacle), `abs` (proof ends in an empty `·` bullet), and `prng2` (depends on `lcg`).

import LtlFrp

namespace Ltl8
open FRP

-- Bit-width bounds vocabulary.
namespace Bounds
abbrev signedHalf (B : Int) : StateProp Int := fun x => -B ≤ x ∧ x < B
abbrev unsignedMax (M : Int) : StateProp Int := fun x => 0 ≤ x ∧ x < M

def u (n : Nat) := unsignedMax (2^n)
def i (n : Nat) := signedHalf (2^(n-1))

abbrev Uint (n : Nat) := { x : Int // Bounds.u n x }
abbrev Sint (n : Nat) := { x : Int // Bounds.i n x }
end Bounds

-- Signed 8-bit multiply-accumulate bound, via the four nonnegative-product lemmas.
example (a w : Int)
    (ha : -128 ≤ a ∧ a < 128) (hw : -128 ≤ w ∧ w < 128) :
    -16256 ≤ a * w ∧ a * w ≤ 16384 := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hw1, hw2⟩ := hw
  have h1 : 0 ≤ (a + 128) * (w + 128) :=
    Int.mul_nonneg (by lia) (by lia)
  have h2 : 0 ≤ (127 - a) * (127 - w) :=
    Int.mul_nonneg (by lia) (by lia)
  have h3 : 0 ≤ (a + 128) * (127 - w) :=
    Int.mul_nonneg (by lia) (by lia)
  have h4 : 0 ≤ (127 - a) * (w + 128) :=
    Int.mul_nonneg (by lia) (by lia)
  constructor <;> lia

-- Bounded-Nat arithmetic: the invariant tracks the numeric upper bound.
namespace Bounded
abbrev boundedBy (k : Nat) : StateProp Nat := fun x => x ≤ k

def add
    (a : □ Nat // (boundedBy n))
    (b : □ Nat // (boundedBy m))
    : □ Nat // boundedBy (n + m) :=
  FRP.RSignal.map2 (fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by lia⟩) a b

def mul
    (a : □ Nat // (boundedBy n))
    (b : □ Nat // (boundedBy m))
    : □ Nat // boundedBy (n * m) :=
  FRP.RSignal.map2  (inv_c := boundedBy (n * m))
 (fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by exact Nat.mul_le_mul hx hy⟩) a b

def example_pipeline
    (a : □ Nat // boundedBy 10)
    (b : □ Nat // boundedBy 10)
    (c : □ Nat // boundedBy 50)
    : □ Nat // boundedBy 150 :=
  add (mul a b) c
end Bounded

end Ltl8
