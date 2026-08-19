import LtlFrp.LTL

namespace Monad
-- ANCHOR: monad
class Monad (m : Type → Type) where
  -- The operations that a monad supports...
  pure : α → m α -- Inject a value into the computational context
  bind : m α → (α → m β) → m β -- Sequence a computation

  -- ...and proofs of the monads laws
  lid: bind (pure a) f = f a
  rid : bind ma pure = ma
  assoc : bind (bind ma f) g = bind ma (fun a => bind (f a) g)
-- ANCHOR_END: monad

-- ANCHOR: monad_ex
inductive Perhaps α where
  | nothing : Perhaps α
  | indeed (a : α) : Perhaps α

instance : Monad Perhaps where
  pure a := Perhaps.indeed a
  bind per f := match per with
    | Perhaps.nothing => Perhaps.nothing
    | Perhaps.indeed a => f a

  lid := by simp
  rid := by intros x ma; cases ma <;> rfl
  assoc := by intros x ma; cases ma <;> simp
-- ANCHOR_END: monad_ex

end Monad

-- ANCHOR: comonad
class Comonad (w : Type → Type) where
  extract : w α → α
  extend  : w α → (w α → β) → w β

  lid: extract (extend wa f) = f wa
  rid: extend wa extract = wa
  assoc: extend (extend wa f) g = extend wa (fun wa' => g (extend wa' f))
-- ANCHOR_END: comonad


namespace Examples

end Examples
