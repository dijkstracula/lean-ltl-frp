import LtlFrp.FRP.Verified

namespace FRP

-- ANCHOR: hoare
abbrev Hoare (P : StateProp α) (Q : StateProp β):=
  (□ α // P) → (□ β // Q)

infixr:35 " ⟹ " => Hoare
-- ANCHOR_END: hoare

-- ANCHOR: refined-value-syntax
syntax "⦃" ident " : " term " // " term "⦄" : term
macro_rules
  | `(⦃$i:ident : $ty // $p⦄) => `((fun $i : $ty => $p : StateProp $ty))
-- ANCHOR_END: refined-value-syntax

-- ANCHOR: hoare-skip
def hoare_skip {P : StateProp α} : ⦃ a : α // P a ⦄ ⟹ ⦃ a : α // P a ⦄ :=
  fun f => f
-- ANCHOR_END: hoare-skip

-- ANCHOR: hoare-seq
def hoare_seq {P : StateProp α} {Q : StateProp β} {R : StateProp γ} :
    (⦃b : β // Q b⦄ ⟹ ⦃c : γ // R c⦄) →
    (⦃a : α // P a⦄ ⟹ ⦃b : β // Q b⦄) →
    (⦃a : α // P a⦄ ⟹ ⦃c : γ // R c⦄) := Function.comp
-- ANCHOR_END: hoare-seq

-- ANCHOR: hoare-if
def hoare_if
  {P : StateProp α} {Q : StateProp β}
  (C : StateProp α) [inst : DecidablePred C]
  (thn : {a : α // P a ∧ C a}   → {b : β // Q b})
  (els : {a : α // P a ∧ ¬ C a} → {b : β // Q b})
  : (⦃a : α // P a⦄ ⟹ ⦃b : β // Q b⦄) := fun sig =>
  (fun ⟨val, prop⟩ => if h : C val
    then thn ⟨val, And.intro prop h⟩
    else els ⟨val, And.intro prop h⟩) <$$> sig
-- ANCHOR_END: hoare-if

-- ANCHOR: iter-one
def iter_one
  (b : StateProp α) [inst : DecidablePred b]
  (step : {a : α // P a ∧ b a} → {a : α  // P a})
  : (□ α // P) → (□ α // P) := hoare_if b step (fun ⟨x, ⟨h_P, _⟩⟩ => ⟨x, h_P⟩)
-- ANCHOR_END: iter-one

-- ANCHOR: event-when
def Event.when
  (P : StateProp α)
  (raise : StateProp α) [DecidablePred raise]
  (sig : □ α // P)
  (hLive : (◇ ⌜raise⌝) sig.val)      -- ◇: `raise` eventually holds
  : ◇ {a : α // P a ∧ raise a} :=
    have hTerm : ∃ t, raise (sig.val t) := (eventually_atom_iff sig.val).mpr hLive
    let toOpt : {a : α // P a} → Option {a : α // P a ∧ raise a} :=
      fun ⟨a, hp⟩ => if h : raise a then some ⟨a, And.intro hp h⟩ else none
    let f : □ (Option {a : α // P a ∧ raise a}) := toOpt <$> sig
    have live : FRP.fires f := by
      unfold FRP.fires
      simp [toOpt, f, Functor.map, FRP.RSignal.split]
      exact hTerm
    { f, live }
-- ANCHOR_END: event-when

-- ANCHOR: rsignal-while
def RSignal.while
  (P b : StateProp α)           -- P, our loop invariant; b, our loop check
  [inst : DecidablePred b]
  (s : □ α // P)                -- our source of input values to poll
  (hLive : (◇ ⌜(¬b ·)⌝) s.val)  -- ◇: we eventually exit the loop
  : ◇ {a : α // P a ∧ ¬b a} := Event.when P (¬b ·) s hLive
-- ANCHOR_END: rsignal-while

end FRP
