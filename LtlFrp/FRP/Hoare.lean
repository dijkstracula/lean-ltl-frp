import LtlFrp.FRP.Refining

namespace FRP.Refining

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

-- ANCHOR: hoare-if-val
def hoare_if_val
  {P : StateProp α} {Q : StateProp β}
  (C : StateProp α) [inst : DecidablePred C]
  (thn : {a : α // P a ∧ C a}   → {b : β // Q b})
  (els : {a : α // P a ∧ ¬ C a} → {b : β // Q b})
  (a : {a : α // P a})
  : {b : β // Q b} :=
  if h : C a.val
  then thn ⟨a.val, And.intro a.property h⟩
  else els ⟨a.val, And.intro a.property h⟩
-- ANCHOR_END: hoare-if-val

-- ANCHOR: hoare-if
def hoare_if
  (C : StateProp α) [inst : DecidablePred C]
  (thn : {a : α // P a ∧ C a}   → {b : β // Q b})
  (els : {a : α // P a ∧ ¬ C a} → {b : β // Q b})
  (input : □ α // P)
  : □ β // Q := hoare_if_val C thn els <$$> input
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
  (hTerm : ∃ t, raise (sig.val t))
  : ◇ {a : α // P a ∧ raise a} :=
    let toOpt : {a : α // P a} → Option {a : α // P a ∧ raise a} :=
      fun ⟨a, hp⟩ => if h : raise a then some ⟨a, And.intro hp h⟩ else none
    let f : □ (Option {a : α // P a ∧ raise a}) := toOpt <$> sig
    have live : FRP.fires f := by
      unfold FRP.fires
      simp [toOpt, f, Functor.map, FRP.Refining.Signal.split]
      exact hTerm
    { f, live }
-- ANCHOR_END: event-when

-- ANCHOR: rsignal-while
def RSignal.while
  (P b : StateProp α)           -- P, our loop invariant; b, our loop check
  [inst : DecidablePred b]
  (s : □ α // P)                -- our source of input values to poll
  (hTerm : ∃ t, ¬ b (s.val t))  -- Proof that we eventually exit the loop
  : ◇ {a : α // P a ∧ ¬b a} := Event.when P (¬b ·) s hTerm
-- ANCHOR_END: rsignal-while

end FRP.Refining
