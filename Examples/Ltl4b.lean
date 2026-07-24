-- Worked example for lean-ltl post 4b ("Reactive Events and LTL.eventually").
-- Machinery this post introduces (Event, fires, merge, latch) lives in LtlFrp.FRP.Signal.

import LtlFrp
import Examples.Ltl4

namespace Ltl4b
open Ltl4

inductive WalkSign where | Walk | DontWalk
deriving Repr, DecidableEq

def pedestrianButton : ◇ Unit := ⟨
  (fun t =>
    match t with
    | 2 | 7 => some ()
    | _ => none),
   ⟨2, by simp⟩⟩

def walkSignal (button : ◇ Unit) : □ WalkSign :=
  fun t => match button t with
    | some () => .Walk
    | none    => .DontWalk

def carLight (button : ◇ Unit) : □ Light :=
  fun t => match button t with
    | some () => .Red
    | none    => cycling t

def pedCrossing (button : ◇ Unit) : □ (Light × WalkSign) :=
  FRP.map2 Prod.mk (carLight button) (walkSignal button)

def onNone : Light → Light
  | .Green => .Yellow
  | .Yellow => .Red
  | .Red => .Green

#eval (List.range 5 : List Time).map (pedCrossing pedestrianButton)

def walkOnlyWhenRed (button : ◇ Unit) : Prop :=
  LTL.always
    (LTL.atom (fun (traffic, ped) => ped = .Walk → traffic = .Red))
    (pedCrossing button)

theorem walkSafe (button : ◇ Unit) : walkOnlyWhenRed button := by
  simp [walkOnlyWhenRed, pedCrossing]
  simp [LTL.always, LTL.atom, now, drop, FRP.map2]
  simp [carLight, walkSignal]
  intro t
  split <;> simp

def spammer : ◇ Unit := ⟨fun _ => some (), ⟨0, by simp⟩⟩

def carsEventuallyGreen (button : ◇ Unit) : Prop :=
  LTL.always (LTL.eventually (LTL.atom (· = .Green)))
    (carLight button)

example : ¬ carsEventuallyGreen spammer := by
  simp [carsEventuallyGreen, spammer]
  simp [LTL.always, LTL.eventually, LTL.atom, now, drop]
  unfold carLight
  simp

end Ltl4b
