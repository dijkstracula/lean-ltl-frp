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

namespace Comonads

-- ANCHOR: comonad_v0
class Comonad (w : Type → Type) where
  extract : w α → α
  extend  : w α → (w α → β) → w β

  lid: extract (extend wa f) = f wa
  rid: extend wa extract = wa
  assoc: extend (extend wa f) g = extend wa (fun wa' => g (extend wa' f))
-- ANCHOR_END: comonad_v0

-- ANCHOR: extend'
def Comonad.extend' [Comonad w] (f : w α → β) (wa : w α) : w β := extend wa f
-- ANCHOR_END: extend'

-- ANCHOR: signal-comonad
instance : Comonad FRP.Signal where
  extract := FRP.now
  extend cm f := f <$> (drop cm)

  lid := by intro α sig β f; unfold FRP.drop; simp [FRP.now, Functor.map, Nat.zero_add]
  rid := by intros α sig; funext t; simp [FRP.now, Functor.map, FRP.drop, Nat.add_zero]
  assoc := by
    intros; funext t
    simp [Functor.map]; unfold FRP.drop Signal.map; simp [Nat.add_assoc]
-- ANCHOR_END: signal-comonad
end Comonads

namespace IMonadV0
-- ANCHOR: imonad_v0
class IMonad (m : StateProp α → Type → Type) where
  -- The operations that an indexed monad supports...
  pure : α → m inv α
  bind : m inv α → (α → m inv β) → m inv β

  -- ...and proofs of the monads laws
  lid: bind (pure a) f = f a
  rid : bind ma pure = ma
  assoc : bind (bind ma f) g = bind ma (fun a => bind (f a) g)

-- ANCHOR_END: imonad_v0

end IMonadV0



end Ltl7
