import LtlFrp
namespace Ltl7
open FRP

-- ANCHOR: next-change-is-small
def sig : □ Float := fun t => 20.0 * t.toFloat.sin

-- "always, the difference between now and next is within tolerance"
def nextChangeIsSmall (δ : Float) : TraceProp Float :=
  □ fun temps => Float.abs (FRP.now temps - FRP.next temps) ≤ δ
-- ANCHOR_END: next-change-is-small

-- ANCHOR: stateprop-review
abbrev signedHalf (B : Int) : StateProp Int := fun x => -B ≤ x ∧ x < B

example : signedHalf 256 99 := by lia
example : signedHalf 256 1000 := by sorry
-- ANCHOR_END: stateprop-review
