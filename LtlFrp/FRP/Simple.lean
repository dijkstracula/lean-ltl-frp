import LtlFrp.Trace

namespace FRP
-- ANCHOR: signal
abbrev Signal α := Time → α
-- ANCHOR_END: signal

-- ANCHOR: fires
def fires (e : Time → Option α) : Prop := ∃ t, (e t).isSome
-- ANCHOR_END: fires

-- ANCHOR: event
structure Event (α : Type) where
  f : Time → Option α
  live : fires f
-- ANCHOR_END: event

-- ANCHOR: event-coefun
instance : CoeFun (Event α) (fun _ => Time → Option α) where
  coe e := e.f
-- ANCHOR_END: event-coefun

-- ANCHOR: event-functor
instance : Functor Event where
  map f ev :=
    let f' := fun t => Option.map f (ev t)
    have staysLive : fires f' := by
      simp [fires, f', Option.isSome_map] at *
      exact ev.live
    {f := f', live := staysLive}
-- ANCHOR_END: event-functor

-- ANCHOR: merge
def merge (e1: Event α) (e2 : Event α) : Event α :=
  let f := fun t => e1 t <|> e2 t
  let fires : fires f := by
    simp [fires, f]
    apply exists_or.mpr
    left ; exact e1.live
  ⟨f, fires⟩
-- ANCHOR_END: merge

-- ANCHOR: latch
def Event.latch (init: α) (e: Event α) : Signal α
  | 0 => (e 0).getD init
  | (n + 1) => (e (n + 1)).getD (latch init e n)
-- ANCHOR_END: latch

-- ANCHOR: clock
def clock : Signal Time := fun t => t
-- ANCHOR_END: clock
-- ANCHOR: advance
def advance (s: Signal α) (t: Time): Signal α := fun n => s (n+t)
-- ANCHOR_END: advance
-- ANCHOR: delay
def delay (s: Signal α) (t: Time): Signal α := fun n => s (n-t)
-- ANCHOR_END: delay

-- ANCHOR: scan
def scan (step : β → β) (init : β) : Signal β :=
  fun n => Nat.rec init (fun _ s => step s) n
-- ANCHOR_END: scan

-- ANCHOR: event-notation
notation "◇ " α => Event α
-- ANCHOR_END: event-notation

-- ANCHOR: signal-const
def Signal.const (v: α) : Signal α := fun _ => v
-- ANCHOR_END: signal-const

-- ANCHOR: signal-map
@[simp]
def Signal.map (f: α → β) (s : Signal α) : Signal β :=
  fun t => f (s t)
-- ANCHOR_END: signal-map

-- ANCHOR: signal-map2
@[simp]
def Signal.map2 (f: α → β → γ) (s1 : Signal α) (s2 : Signal β) : Signal γ :=
  fun t => f (s1 t) (s2 t)
-- ANCHOR_END: signal-map2

-- ANCHOR: signal-map3
def Signal.map3 (f: α → β → γ → δ) (s1 : Signal α) (s2 : Signal β) (s3: Signal γ): Signal δ :=
  fun t => f (s1 t) (s2 t) (s3 t)
-- ANCHOR_END: signal-map3

-- ANCHOR: signal-functor
instance : Functor Signal where
  map := Signal.map
-- ANCHOR_END: signal-functor

-- ANCHOR: signal-applicative
instance : Applicative Signal where
  pure := Signal.const
  seq sf sx := Signal.map2 (· ·) sf (sx ())
-- ANCHOR_END: signal-applicative

end FRP
