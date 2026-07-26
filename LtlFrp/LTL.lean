import LtlFrp.Trace

namespace LTL

-- ANCHOR: atom
def atom (p : σ → Prop) (t : Trace σ) : Prop := p (now t)
-- ANCHOR_END: atom
-- ANCHOR: next
def next (p : Trace σ → Prop) (t : Trace σ) : Prop := p (drop 1 t)
-- ANCHOR_END: next

-- ANCHOR: always
def always (p : Trace σ → Prop) (t : Trace σ) : Prop :=
  ∀ i, p (drop i t)
-- ANCHOR_END: always

-- ANCHOR: eventually
def eventually (p : Trace σ → Prop) (t : Trace σ) : Prop :=
  ∃ i, p (drop i t)
-- ANCHOR_END: eventually

-- ANCHOR: until
def until_then (p1 : Trace σ → Prop) (p2 : Trace σ → Prop) (t : Trace σ) : Prop :=
  ∃ n, (∀ i, i < n → p1 (drop i t)) ∧ p2 (drop n t)
-- ANCHOR_END: until

-- ANCHOR: ltl-notation
prefix:max "□ " => always
prefix:max "◇ " => eventually
prefix:max "○ " => next
infixr:55 " U " => LTL.until_then
notation:max "⌜" p "⌝" => LTL.atom p
-- ANCHOR_END: ltl-notation

-- "True" as a trace predicate: holds for any trace, at any time
-- ANCHOR: true
@[simp]
def true : σ → Prop := (fun _ => True)
-- ANCHOR_END: true

-- "Not" negates `p` at every step in the trace.
-- ANCHOR: not
def not (p : Trace σ → Prop) : Trace σ → Prop := (fun t => ¬ p t)
-- ANCHOR_END: not

-- ANCHOR: implies
def implies (p q : TraceProp σ) : TraceProp σ :=
    fun t => p t → q t

infixr:20 " ⟹ " => implies
-- ANCHOR_END: implies


-- ANCHOR: eventually-as-until
example : ◇ p = true U p := by
  unfold eventually
  unfold until_then
  simp
-- ANCHOR_END: eventually-as-until

-- always p means it's not the case that eventually, not p
-- ANCHOR: always-as-until
example : □ p = not (true U not p) := by
  unfold always
  unfold until_then
  unfold not
  simp
-- ANCHOR_END: always-as-until

end LTL
