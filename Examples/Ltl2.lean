-- Worked example for lean-ltl post 2 ("Execution traces").
-- Machinery this post introduces (Time / Trace / now / drop) lives in LtlFrp.Trace.

import LtlFrp
import Examples.Ltl1

namespace VM

def orangeTrace :=
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by decide)
  let s2 := vmStep s1 .DropCoin (by decide)
  let s3 := vmStep s2 (.Choose .LemonLime) (by decide)
  let s4 := vmStep s3 .TakeItem (by decide)
  let steps := [s0, s1, s2, s3, s4]
  fun n => if H : n < steps.length then steps.get (Fin.mk n H) else s4

#eval orangeTrace 0
#eval orangeTrace 3
#eval orangeTrace 42

def hopperEmpty (s: VMState) : Prop := s.coins = 0

example : hopperEmpty (orangeTrace 0) := by rfl

end VM
