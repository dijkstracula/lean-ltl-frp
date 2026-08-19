-- Worked example for lean-ltl post 7b ("Hoare Logic and loop invariants redux").
-- The combinators this post is about (hoare_skip / hoare_seq / hoare_if / iter_one /
-- Event.when / RSignal.while, plus <$$>, ⦃⦄, ⟹) live in LtlFrp.FRP.Hoare and
-- LtlFrp.FRP.

import LtlFrp

def Nat.factorial : Nat → Nat
| 0 => 1
| (n + 1) => (n + 1) * n.factorial

namespace Ltl7
open FRP

-- The Hoare rules are functor laws: skip = identity map, seq = composition.
example : hoare_seq (g <$$> ·) (f <$$> ·) = (g <$$> f <$$> ·) := by rfl

example {P : StateProp α}
    (f : {a : α // P a} → {a : α // P a}) :
    ∀ s, hoare_skip (f <$$> s) = (f <$$> s) := by intro s; rfl

example {P : StateProp α} {Q : StateProp β} {R : StateProp γ}
        (f : {a : α // P a} → {b : β // Q b})
        (g : {b : β // Q b} → {c : γ // R c}) :
    -- NOTE: argument order matches the library `hoare_seq := Function.comp`;
    -- the scratch wrote this in the opposite (flip-comp) order.
    hoare_seq (g <$$> ·) (f <$$> ·) = ((g ∘ f) <$$> ·) := by rfl

-- A two-step refinement pipeline: {i = 0} ⟹ {i > 0} ⟹ {i ≥ 0}.
namespace IncrSqrt
def incr (i : {i : Int // i = 0}) : {i : Int // i > 0} := ⟨i.val + 1, by lia⟩
def sqrt (i : {i : Int // i > 0}) : {i : Int // i >= 0} := ⟨i.val, by lia⟩

#check (incr <$$> ·)

def incr_sig : ⦃ i : Int // i = 0 ⦄ ⟹ ⦃ i : Int // i > 0 ⦄ := FRP.RSignal.map incr
def sqrt_sig : ⦃ i : Int // i > 0 ⦄ ⟹ ⦃ i : Int // i ≥ 0 ⦄ := FRP.RSignal.map sqrt

def z : □ Int // (· = 0)  := FRP.RSignal.const ⟨0, by lia⟩
def z2 : □ Int // (· > 0) := incr_sig z
def z3 : □ Int // (· ≥ 0) := sqrt_sig z2

#check (FRP.RSignal.weaken (by lia) : □ Int // (· = 0) → □ Int // (· >= 0))
end IncrSqrt

-- Combining two constant signals with map2.
namespace AddDemo
def z1 : □ Int // (· = 5)  := FRP.RSignal.const ⟨5, by lia⟩
def z2 : □ Int // (· = 7)  := FRP.RSignal.const ⟨7, by lia⟩
def z3 : □ Int // (· > 10) :=
  FRP.RSignal.map2 (fun ⟨a, ah⟩ ⟨b, bh⟩ => ⟨a + b, by lia⟩) z1 z2
end AddDemo

-- Syracuse / Collatz: hoare_if picks the even/odd branch, preserving n > 0.
def syra_even : {n : Int // n > 0 ∧ n % 2 = 0} → {m : Int // m > 0} :=
  fun ⟨n, ⟨hPos, hEven⟩⟩ => ⟨n / 2, by omega⟩

def syra_odd : {n : Int // n > 0 ∧ ¬ (n % 2 = 0)} → {m : Int // m > 0} :=
  fun ⟨n, ⟨hPos, hOdd⟩⟩ => ⟨(3*n + 1)/2, by omega⟩

def syra_step_val : {n : Int // n > 0} → {n : Int // n > 0} :=
  fun ⟨n, hPos⟩ =>
    if h : n % 2 = 0
    then syra_even ⟨n, ⟨hPos, h⟩⟩
    else syra_odd ⟨n, ⟨hPos, h⟩⟩

def syra : (□ Int // (· > 0)) → (□ Int // (· > 0)) :=
  hoare_if (· % 2 = 0) syra_even syra_odd

def positives : □ Int // (· > 0) :=
  FRP.RSignal.collect (fun t => ⟨ Int.ofNat t + 1, by lia⟩)

def syracuse_trajectory (n : Int) (h_pos : n > 0) : □ Int // (· > 0) :=
  FRP.scan syra_step_val ⟨n, h_pos⟩

#eval (List.range 10) |>.map (syracuse_trajectory 42 (by lia)).val

def trajectory (n : Int) (hPos : 0 < n) : □ Int // (· > 0) :=
  FRP.scan syra_step_val ⟨n, hPos⟩

#eval (List.range 10) |>.map (trajectory 10 (by lia)).val

-- Factorial loop with the invariant z = i!.
namespace Fact
def fact_inv (_ : Nat) : StateProp (Nat × Nat) :=
  fun (i, z) => z = i.factorial

def i : □ Nat := FRP.scan (· + 1) 0
def z : □ Nat := (·.factorial) <$> i

def fact_loop : □ (Nat × Nat) // (fun ⟨i, z⟩ => z = i.factorial) :=
  let s : □ (Nat × Nat) := Prod.mk <$> i <*> z
  have inv : ∀ t, (s t).2 = (s t).1.factorial := by intro t; rfl
  FRP.RSignal.collect (fun t => ⟨s t, inv t⟩)

#eval (fact_loop.val 5)

def fact_step (n : Nat) : {env // fact_inv n env} → {env // fact_inv n env} :=
  fun ⟨(i, z), HFact⟩ =>
    if h : i < n
    then ⟨(i+1, z*(i+1)), by
      rw [HFact]; simp [fact_inv, Nat.factorial]; lia⟩
    else ⟨(i, z), HFact⟩

-- DROPPED (broken WIP in the scratch): `fact_done`, the "while i < n" exit event via
-- RSignal.while. Its termination witness `⟨n, by …⟩` fails — the proof reduces to `False`.
end Fact

def counterEvent (n : Nat) (h : n > 0) : FRP.Event Int :=
  let f t := if 1 ≤ t ∧ t ≤ n then some (t : Int) else none
  have live : FRP.fires f := ⟨1, by simp [f]; lia⟩
  {f, live}

end Ltl7
