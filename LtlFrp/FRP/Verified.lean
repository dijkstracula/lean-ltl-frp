import LtlFrp.LTL
import LtlFrp.FRP.Simple
import Std.Tactic.BVDecide

namespace FRP

-- ANCHOR: always-iff
-- The reflection at its most general: `□` unpacks to a `∀` over time, definitionally.
theorem always_iff {ψ : TraceProp β} (sig : Signal β) :
    (∀ i, ψ (drop i sig)) ↔ (□ ψ) sig := Iff.rfl
-- ANCHOR_END: always-iff

-- ANCHOR: always-atom-iff
-- The `∀`-bridge for atoms: the shape of a safety obligation. With `drop` putting the offset
-- first, `⌜inv⌝ (drop i sig)` reduces to `inv (sig i)`, so this is `always_iff` verbatim.
theorem always_atom_iff {inv : StateProp β} (sig : Signal β) :
    (∀ t, inv (sig t)) ↔ (□ ⌜inv⌝) sig := always_iff (ψ := ⌜inv⌝) sig
-- ANCHOR_END: always-atom-iff

-- ANCHOR: eventually-atom-iff
-- The `∃`-bridge for atoms: the shape of a liveness obligation. Also definitional now.
theorem eventually_atom_iff {inv : StateProp β} (sig : Signal β) :
    (∃ t, inv (sig t)) ↔ (◇ ⌜inv⌝) sig := Iff.rfl
-- ANCHOR_END: eventually-atom-iff

-- ANCHOR: until-atom-iff
-- The mixed bridge: `U` reflects a bounded `∃∀` — the loop invariant (the `∀`-prefix)
-- and its termination witness (the `∃ n`), in one formula.
theorem until_atom_iff {inv done : StateProp β} (sig : Signal β) :
    (∃ n, (∀ i, i < n → inv (sig i)) ∧ done (sig n))
      ↔ (⌜inv⌝ U ⌜done⌝) sig := Iff.rfl
-- ANCHOR_END: until-atom-iff

-- ANCHOR: rsignal
abbrev RSignal (α : Type) (inv : StateProp α) :=
  { s : Signal α // (□ ⌜inv⌝) s }
-- ANCHOR_END: rsignal

structure RS (α : Type) where
  sig : Signal α
  sp: StateProp α
  inv : (□ ⌜sp⌝) sig

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

-- ANCHOR: rsignal-split
def RSignal.split (sig: (□ β) // inv) : □ (β // inv) :=
  let vals : □ β := sig.val
  let safety : ∀ t, inv (vals t) := (always_atom_iff vals).mpr sig.property
  fun t => ⟨ vals t, safety t ⟩
-- ANCHOR_END: rsignal-split

-- ANCHOR: rsignal-collect
def RSignal.collect (sig : □ (β // inv)) : (□ β) // inv :=
  let vals : □ β := fun t => (sig t).val
  let safety : (□ ⌜inv⌝) vals := (always_atom_iff vals).mp (fun t => (sig t).property)
  ⟨ vals, safety ⟩
-- ANCHOR_END: rsignal-collect

-- ANCHOR: rsignal-delay
def RSignal.delay (s: □ α // inv) (n: Time): □ α // inv :=
  (fun t => RSignal.split s (t-n)) |> RSignal.collect
-- ANCHOR_END: rsignal-delay

-- ANCHOR: coe-refine
instance : Coe ((□ α) // inv) (□ (α // inv)) where
  coe := RSignal.split

instance : Coe (□ (α // inv)) ((□ α) // inv) where
  coe := RSignal.collect
-- ANCHOR_END: coe-refine

-- ANCHOR: rsignal-accumulate
def RSignal.accumulate
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

  RSignal.collect step_at
-- ANCHOR_END: rsignal-accumulate

-- ANCHOR: rsignal-const
def RSignal.const (a : { a : α // inv a } ) : □ α // inv :=
  RSignal.collect (fun _ => a)
-- ANCHOR_END: rsignal-const

-- ANCHOR: rsignal-map
def RSignal.map
  {pre: α → Prop}
  {post: β → Prop}
  (f: {a: α // pre a} → {b : β // post b})
  : (□ α // pre) → (□ β // post) := fun s =>
    (fun t => f (RSignal.split s t)) |> RSignal.collect
-- ANCHOR_END: rsignal-map

-- ANCHOR: rsignal-map2
def RSignal.map2
  {inv_a: α → Prop} {inv_b: β → Prop} {inv_c: γ → Prop}
  (f: {a: α // inv_a a} → {b : β // inv_b b} → {c : γ // inv_c c})
  (s1: □ α // inv_a) (s2: □ β // inv_b)
  : □ γ // inv_c :=
  (fun t => f (RSignal.split s1 t) (RSignal.split s2 t)) |> RSignal.collect
-- ANCHOR_END: rsignal-map2

-- ANCHOR: rsignal-weaken
def RSignal.weaken {P Q : StateProp α}
  (h : ∀ a, P a → Q a) : (□ α // P) → □ α // Q :=
    FRP.RSignal.map (fun ⟨val, prop⟩ => ⟨val, h val prop⟩)
-- ANCHOR_END: rsignal-weaken

-- ANCHOR: dollar-map
infixr:100 " <$$> " => FRP.RSignal.map
-- ANCHOR_END: dollar-map

-- ANCHOR: accumulate
def accumulate
  (init : β)
  (onNone: β → β )
  (onSome: α → β → β)
  (ev: Event α)
  : Signal β := RSignal.accumulate
  ⟨init, by trivial⟩
  (fun s => ⟨onNone s, by trivial⟩)
  (fun e s => ⟨onSome e s, by trivial⟩)
  ev
-- ANCHOR_END: accumulate

end FRP
