-- Worked example for lean-ltl post 1 ("Reactive Programming in Lean 4").
-- Transition-system vending machine. Predates the library — no LtlFrp imports.

namespace VM

inductive Flavour where
  | Orange
  | LemonLime
deriving Repr

structure VMState where
  coins: Nat
  dispensed: Option Flavour
  numOrange : Nat
  numLL : Nat
deriving Repr

-- Actions

inductive VMAction where
  | DropCoin
  | Choose : Flavour → VMAction
  | Restock
  | TakeItem
deriving Repr

@[simp]
def validAction (s : VMState) (a : VMAction) : Prop :=
  match a with
  | .DropCoin          => True
  | .Restock           => True
  | .Choose .Orange    => s.coins >= 2 ∧ s.numOrange > 0
  | .Choose .LemonLime => s.coins >= 2 ∧ s.numLL > 0
  | .TakeItem          => Option.isSome s.dispensed

instance (s : VMState) (a : VMAction) : Decidable (validAction s a) := by
  simp; split <;> infer_instance

def init : VMState := {
  coins := 0, dispensed := none, numOrange := 5, numLL := 5
}

def vmStep (s : VMState)
           (a : VMAction)
           (H : validAction s a)
           : VMState :=
  match a with
  | .DropCoin        => { s with coins := s.coins + 1 }
  | .TakeItem        => { s with dispensed := none }
  | .Choose .Orange  => { s with
    coins     := s.coins - 2,
    numOrange := s.numOrange - 1
    dispensed := some .Orange,
  }
  | .Choose .LemonLime => { s with
    coins     := s.coins - 2,
    numLL     := s.numLL - 1
    dispensed := some .LemonLime,
  }
  | .Restock         => init

abbrev TSM α := StateT VMState (Except String) α

def perform (a : VMAction) : TSM Unit := do
  let s ← get
  if h : validAction s a then
    let s' := vmStep s a h
    set s'
  else Except.error s!"Invalid action {repr a} in state {repr s}"

def take : TSM Flavour := do
  let s ← get
  if H : validAction s .TakeItem then
    perform .TakeItem
    pure (Option.get s.dispensed H)
  else Except.error s!"Nothing to take in state {repr s}"

def getOrange : TSM Flavour := do
  perform (.DropCoin)
  perform (.DropCoin)
  perform (.Choose .LemonLime)
  take

end VM
