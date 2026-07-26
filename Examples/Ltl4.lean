-- Worked example for lean-ltl post 4 ("Reactive Signals and LTL.always").
-- Machinery this post introduces (Signal, map/map2, clock/advance, ...) lives in LtlFrp.FRP.Simple.

import LtlFrp

namespace Ltl4

inductive Light where | Red | Yellow | Green
deriving Repr

def cycling : FRP.Signal Light :=
  fun n =>
    have h : n % 3 < 3 := Nat.mod_lt n (by lia)
    match n % 3, h with
    | 0, _ => .Red
    | 1, _ => .Yellow
    | 2, _ => .Green

def l1 : □ Light := cycling
def l2 : □ Light := FRP.advance cycling 1
def junction : □ (Light × Light) := FRP.Signal.map2 Prod.mk l1 l2

#eval junction 5

def neverBothGreen : Prop :=
  LTL.always (LTL.not ⌜fun (l1, l2) => (l1 = .Green ∧ l2 = .Green)⌝) junction

example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.Signal.map2, FRP.advance]
  simp [cycling]
  split <;> split <;> simp
  lia

end Ltl4
