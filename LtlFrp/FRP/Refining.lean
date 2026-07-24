import LtlFrp.LTL
import LtlFrp.FRP.Signal
import Std.Tactic.BVDecide

namespace FRP

-- ANCHOR: always-atom-iff
theorem always_atom_iff {inv : StateProp β} (sig : Signal β) :
  (∀ t, inv (sig t)) ↔ (□ (LTL.atom inv)) sig := by
  constructor
  · intro h t ; simp [LTL.atom, drop, now] ; exact h t
  · simp [LTL.always, LTL.atom, drop, now]
-- ANCHOR_END: always-atom-iff

namespace Refining

-- ANCHOR: rsignal
abbrev RSignal (α : Type) (inv : StateProp α) :=
  { s : Signal α // (□ (LTL.atom inv)) s }
-- ANCHOR_END: rsignal

structure RS (α : Type) where
  sig : Signal α
  sp: StateProp α
  inv : (□ (LTL.atom sp)) sig

  -- ANCHOR: signal-syntax
  declare_syntax_cat signalTree
  syntax (name := signalLift) signalTree : term

  syntax (name := signalRaw) "□ " term:max : signalTree
  syntax (name := refinedSig) signalTree " // " term:51 : term
  syntax (name := outerRefinedSig) "(" signalTree ")" " // " term:51 : term
  syntax (name := pointwiseRefined) "□ " "(" term " // " term ")" : term
  -- ANCHOR_END: signal-syntax

  -- ANCHOR: signal-macros
  macro_rules (kind := signalLift)
    | `(□ $α) => `(Signal $α)

  macro_rules (kind := refinedSig)
    | `(□ $α // $inv) => `(RSignal $α $inv)

  macro_rules (kind := outerRefinedSig)
    | `((□ $α) // $inv) => `(RSignal $α $inv)

  macro_rules (kind := pointwiseRefined)
    | `(□ ($α // $inv)) => `(Signal { x : $α // $inv x })
  -- ANCHOR_END: signal-macros

-- ANCHOR: coe-trivial
instance {inv : α → Prop} : CoeHead ((□ α) // inv) (□ α) where
  coe rs := rs.val

instance : Coe (Signal α) ((□ α) // (fun _ => True)) where
  coe s := ⟨s, (always_atom_iff s).mp (fun _ => trivial)⟩
-- ANCHOR_END: coe-trivial

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

-- ANCHOR: split
def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
  let vals : □ β := sig.val
  let safety : ∀ t, inv (vals t) := (always_atom_iff vals).mpr sig.property
  fun t => ⟨ vals t, safety t ⟩
-- ANCHOR_END: split

-- ANCHOR: collect
def Signal.collect (sig : □ (β // inv)) : (□ β) // inv :=
  let vals : □ β := fun t => (sig t).val
  let safety : (□ (LTL.atom inv)) vals := (always_atom_iff vals).mp (fun t => (sig t).property)
  ⟨ vals, safety ⟩
-- ANCHOR_END: collect

-- ANCHOR: rsignal-delay
def RSignal.delay (s: □ α // inv) (n: Time): □ α // inv :=
  (fun t => Signal.split s (t-n)) |> Signal.collect
-- ANCHOR_END: rsignal-delay

-- ANCHOR: coe-refine
instance : Coe ((□ α) // inv) (□ (α // inv)) where
  coe := Signal.split

instance : Coe (□ (α // inv)) ((□ α) // inv) where
  coe := Signal.collect
-- ANCHOR_END: coe-refine

-- ANCHOR: refining-accumulate
def accumulate
  {inv: β → Prop}
  (init : { s : β // inv s })
  (onNone: { s: β // inv s } → { s': β // inv s' })
  (onSome: α → { s: β // inv s} → {s': β // inv s'})
  (ev: Event α)
  : (□ β) // inv :=
  let switch (t: Time) : {s: β // inv s} → {s': β // inv s'} :=
    match ev t with
    | none => onNone
    | some a => onSome a

  let step_at : □ (β // inv) := fun n => Nat.rec
    init
    switch n

  Signal.collect step_at
-- ANCHOR_END: refining-accumulate

-- ANCHOR: rsignal-const
def RSignal.const (a : { a : α // inv a } ) : □ α // inv :=
  Signal.collect (fun _ => a)
-- ANCHOR_END: rsignal-const

-- ANCHOR: rsignal-map
def map
  {pre: α → Prop}
  {post: β → Prop}
  (f: {a: α // pre a} → {b : β // post b})
  : ⦃ a : α // pre a ⦄ ⟹ ⦃ b : β // post b ⦄ := fun s =>
    (fun t => f (Signal.split s t)) |> Signal.collect
-- ANCHOR_END: rsignal-map

-- ANCHOR: rsignal-map2
def map2
  {inv_a: α → Prop} {inv_b: β → Prop} {inv_c: γ → Prop}
  (f: {a: α // inv_a a} → {b : β // inv_b b} → {c : γ // inv_c c})
  (s1: □ α // inv_a) (s2: □ β // inv_b)
  : □ γ // inv_c :=
  (fun t => f (Signal.split s1 t) (Signal.split s2 t)) |> Signal.collect
-- ANCHOR_END: rsignal-map2

-- ANCHOR: rsignal-weaken
def RSignal.weaken {P Q : StateProp α}
  (h : ∀ a, P a → Q a) : (□ α // P) → □ α // Q :=
    FRP.Refining.map (fun ⟨val, prop⟩ => ⟨val, h val prop⟩)
-- ANCHOR_END: rsignal-weaken

-- ANCHOR: dollar-map
infixr:100 " <$$> " => FRP.Refining.map
-- ANCHOR_END: dollar-map

end Refining

-- ANCHOR: accumulate
def accumulate
  (init : β)
  (onNone: β → β )
  (onSome: α → β → β)
  (ev: Event α)
  : Signal β := Refining.accumulate
  ⟨init, by trivial⟩
  (fun s => ⟨onNone s, by trivial⟩)
  (fun e s => ⟨onSome e s, by trivial⟩)
  ev
-- ANCHOR_END: accumulate

end FRP
