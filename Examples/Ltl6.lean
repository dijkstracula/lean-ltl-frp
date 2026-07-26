-- Worked example for lean-ltl post 6 ("Composing invariant-transforming combinators").
-- The reusable machinery this post introduces (RSignal, □//, split/collect, refined
-- map/map2/weaken) lives in LtlFrp.FRP.Verified and is anchored there.
--
-- Dropped from the scratch (WIP / broken): `popcount` (proof term `Nat.lt_of_le_of_lt`
-- has no arguments) and `segment286_unsetA20` (references undefined `a20Masked`).

import LtlFrp

namespace Ltl6
open FRP

abbrev signedHalf (B : Int) : StateProp Int := fun x => -B ≤ x ∧ x < B
abbrev unsignedMax (M : Int) : StateProp Int := fun x => 0 ≤ x ∧ x < M

def lcg (x : Int) : Int := (5 * x + 17) % 256

def prng : □ Int // unsignedMax 256
  := FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by simp [unsignedMax, lcg]; lia ⟩ )
              ⟨97, by trivial⟩
     |> RSignal.collect

def ss : □ Int // unsignedMax (2^16) := RSignal.const ⟨0xFFFF, by lia⟩

def incr_from (off: Int): □ Int // unsignedMax (2^16) :=
  RSignal.collect fun i => ⟨(off + i) % (2^16), by lia⟩

def widenedOnePadded : (□ Int // unsignedMax (2^8)) → (□ Int // unsignedMax (2^16)) :=
  FRP.RSignal.map (fun ⟨i, hi⟩ => ⟨0xFF00 + i, by lia⟩)

def bankedMemory (page : {p : Int // unsignedMax (2^8) p})
  : (□ Int // unsignedMax (2^8)) → (□ Int // unsignedMax (2^16)) :=
  FRP.RSignal.map (fun ⟨i, hi⟩ => ⟨page * 256 + i, by lia⟩)

def Segment8086 : (□ Int // unsignedMax (2^16)) →
                  (□ Int // unsignedMax (2^16)) →
                  (□ Int // unsignedMax (2^20)) :=
  FRP.RSignal.map2
  (fun ⟨base, hb⟩ ⟨off, ho⟩ => ⟨(base * 16 + off) % (2^20), by lia⟩)

abbrev a20Enabled (ptr : Int) : Prop :=
  unsignedMax (2^24) ptr

abbrev a20Disabled (ptr : Int) : Prop :=
  unsignedMax (2^24) ptr ∧ (ptr / 2^20) % 2 = 0

example : (0xF01D * 16 + 0xFEF0) % 2^20 = 0x000C0 := by lia
example : (0xF01D * 16 + 0xFEF0)        ≠ 0x000C0 := by lia

def x86RealMode : (□ Int // unsignedMax (2^16)) →
                  (□ Int // unsignedMax (2^16)) →
                  (□ Int // unsignedMax (2^20 + 2^16 - 16)) :=
  FRP.RSignal.map2
  (fun ⟨base, hb⟩ ⟨off, ho⟩ => ⟨(base * 16 + off), by lia⟩)

def a20_off_286_from_8086 (sig_8086 : □ Int // unsignedMax (2^20)) : □ Int // a20Enabled :=
  RSignal.weaken (by lia) sig_8086

def a20_down_from_a20_up (sig_8086 : □ Int // a20Enabled) : □ Int // a20Disabled :=
  FRP.RSignal.map (fun ⟨ptr, inv⟩ =>
    -- ptr && !(1 << 20)
    ⟨ptr - 2^20 * (ptr / 2^20 % 2), by lia⟩)
    sig_8086

#eval List.range 20
  |>.map (x86RealMode ss (incr_from 0xFFFFD)).val
  |>.map (BitVec.ofInt 20 ·)

theorem a20_high_order_bits_unset
  (base off : {a : Int // unsignedMax (2^16) a})
  : (base.val * 16 + off.val) / 2^21 = 0 := by lia

end Ltl6
