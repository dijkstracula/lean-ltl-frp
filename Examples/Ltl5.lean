-- Worked example for lean-ltl post 5 ("Stateful combinators, safety, and liveness").
-- Machinery this post introduces (scan, accumulate) lives in LtlFrp.FRP.Signal / LtlFrp.FRP.Refining.

import LtlFrp

namespace Ltl5

def screaming : FRP.Signal String := FRP.scan (· ++ "a") ""
#eval (List.range 5).map screaming

namespace CrossingState
  inductive CrossingState where
    | Idle                             -- Traffic light runs as usual
    | Countdown : Nat → CrossingState  -- N more walk ticks after this one
    | Cooldown  : Nat → CrossingState  -- N more cooldown ticks after this one
  deriving Repr

  def fold (idle : β) (countdown : Nat → β) (cooldown : Nat → β) : CrossingState → β
  | .Idle => idle
  | .Countdown n => countdown n
  | .Cooldown n => cooldown n

  abbrev bounded : CrossingState → Prop
  | .Idle        => True
  | .Countdown n => 0 <= n ∧ n < 8
  | .Cooldown n  => 0 <= n ∧ n < 8

  def tick : { s: CrossingState // bounded s } → { s': CrossingState // bounded s' }
    | ⟨.Idle, _ ⟩        => ⟨ .Idle, by trivial ⟩
    | ⟨.Cooldown 0, _ ⟩  => ⟨ .Idle, by trivial ⟩
    | ⟨.Cooldown (n+1), _ ⟩  => ⟨ .Cooldown n, by lia⟩
    | ⟨.Countdown 0, _ ⟩     => ⟨ .Cooldown 3, by trivial ⟩
    | ⟨.Countdown (n+1), _ ⟩ => ⟨ .Countdown n, by lia ⟩

  def onNone : { s: CrossingState // bounded s } → { s': CrossingState // bounded s' } := tick

  def onSome (_ev : Unit) : { s: CrossingState // bounded s } → { s': CrossingState // bounded s' } := fun
    | ⟨.Idle, h⟩ => ⟨ .Countdown 3, by lia ⟩
    | s => tick s

end CrossingState

def presses : ◇ Unit :=
  let f := fun
  | 2 | 5 => some ()
  | _ => none

  ⟨ f, by exists 2 ⟩

def spammer : ◇ Unit :=
  let f := fun | _ => some ()
  ⟨ f, by exists 2 ⟩

end Ltl5
