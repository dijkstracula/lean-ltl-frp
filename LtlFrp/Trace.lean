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
abbrev StateProp σ := σ → Prop
-- ANCHOR_END: state-prop
-- ANCHOR: trace-prop
abbrev TraceProp σ := (Trace σ → Prop)
-- ANCHOR_END: trace-prop
