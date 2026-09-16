-- example code for lean-ltl-7

import LtlFrp

namespace Ltl7b
open FRP

namespace Monads

-- ANCHOR: monad_signal_v0
instance : Monad FRP.Signal where
  pure := Signal.const
  bind := fun s f => fun t => (f <$> s) t t
-- ANCHOR_END: monad_signal_v0

end Monads

namespace Comonads
-- ANCHOR: comonad_v0
class Comonad (w : Type → Type) where
  extract : w α → α
  extend  : w α → (w α → β) → w β

class LawfulComonad w extends Comonad w where
  lid: extract (extend wa f) = f wa
  rid: extend wa extract = wa
  assoc: extend (extend wa f) g = extend wa (fun wa' => g (extend wa' f))
-- ANCHOR_END: comonad_v0

-- ANCHOR: extend'
@[simp]
def Comonad.extend' [Comonad w] : (w α → β) → w α → w β := flip extend
-- ANCHOR_END: extend'

namespace coKleisli_v0
-- ANCHOR: coKleisli_v0
@[simp]
def comonad_composition [Comonad w]: (w γ → β) → (w α → γ) → (w α → β) :=
  fun g f => g ∘ (Comonad.extend' f)

infixr:95 " =<= " => comonad_composition
-- ANCHOR_END: coKleisli_v0

open Comonad

-- ANCHOR: coKleisli_v0_laws
theorem lid_equiv [Comonad w] (f : w α → β):
      (extract =<= f = f)
        ↔
      (∀ wa : w α, extract (extend wa f) = f wa) := by
  simp [comonad_composition]; unfold Function.comp
  constructor
  · intro h wa
    change (fun wa => extract (extend wa f)) = f at h
    apply congrFun h wa
  · intro h
    funext wa
    exact h wa

theorem rid_equiv [Comonad w] (f : w α → β) :
  (f =<= extract = f)
    ↔
  (∀ wa : w α, extend wa extract = wa) := by sorry

theorem fusion [Comonad w]
    (f : w α → β)
    (g : w β → γ)
  : extend' g ∘ extend' f = extend' (g =<= f) := by sorry

-- ANCHOR_END: coKleisli_v0_laws

end coKleisli_v0

-- ANCHOR: signal-comonad
instance : LawfulComonad FRP.Signal where
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

end Ltl7b
