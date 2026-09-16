-- ANCHOR: time
abbrev Time := Nat
-- ANCHOR_END: time
-- ANCHOR: trace
abbrev Trace σ := Nat → σ
-- ANCHOR_END: trace

-- ANCHOR: now
def now (t : Trace σ) : σ := t 0
-- ANCHOR_END: now
-- ANCHOR: drop
def drop (n : Nat) (t : Trace σ) : Trace σ := fun n' => t (n + n')
-- ANCHOR_END: drop

-- ANCHOR: state-prop
-- A StateProp produces a logical propostion, given a particular σ.
-- (`split` and `collect` lifts a StateProp in and out of safety property-ness.)
abbrev StateProp σ := σ → Prop
-- ANCHOR_END: state-prop
-- ANCHOR: trace-prop
-- A TraceProp produces a logical propostion given a full execution trace.
-- (Recall: `Trace a := Nat → a`, the same type as a Signal!)
abbrev TraceProp σ := (Trace σ → Prop)
-- ANCHOR_END: trace-prop

-- ANCHOR: models
def models (t : Trace σ) (φ : TraceProp σ) : Prop := φ t
infix:45 " ⊨ " => models
-- ANCHOR_END: models
