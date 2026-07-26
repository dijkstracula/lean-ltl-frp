-- Worked example for lean-ltl post 3 ("A Deep Embedding of Linear Temporal Logic").
-- The LTL operators this post introduces now live in LtlFrp.LTL.

import LtlFrp
import Examples.Ltl2

namespace VM.LTLTheorems
open LTL

def validTrace (t : Trace VMState) : Prop :=
  t 0 = init ∧
  ∀ i, ∃ a, ∃ h : validAction (t i) a, t (i + 1) = vmStep (t i) a h

def noFreeLunch : TraceProp VMState :=
  □ (⌜fun s => s.dispensed.isNone ∧ s.coins < 2⌝ ⟹
    (○ ⌜fun s => s.dispensed.isNone⌝))

theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t ⟨Hinit, Hcons⟩
  simp [noFreeLunch, always, implies, next, atom, now, drop]
  intro i Hempty Hunpaid
  have ⟨a, h_valid, h_step⟩ := Hcons i
  unfold vmStep at h_step
  cases a <;> simp at h_step <;> simp [h_step]
  case Restock => rfl
  case DropCoin => assumption
  case Choose f =>
    cases f <;> simp <;> simp at h_step <;> simp at h_valid <;> lia

def hopperEmpty (s: VMState) : Prop := s.coins = 0
def isCurrentlyEmpty := ⌜hopperEmpty⌝

def mustPayFirst : Trace VMState → Prop :=
  ⌜(·.dispensed = none)⌝ U ⌜(·.coins ≥ 2)⌝

end VM.LTLTheorems
