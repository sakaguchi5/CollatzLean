import CollatzLean.Collatz.OddOrbit.Basic
import CollatzLean.Collatz.Word.Periodic
import Mathlib.Tactic.Ring

/-!
# 周期指数tailの有限語反復への還元

指数tailが周期`q`を持つなら、周期境界ごとの各`q`-segmentは同じ有限wordである。
従って、その一周期wordがexpandingなら、有限語の無限反復排除定理に反する。

無限軌道固有の薄いadapterだけをここへ置く。
-/

namespace Collatz
namespace OddOrbit

/-- 指数tailが`q`周期なら、`k`周期後の各指数は元の指数と一致する。 -/
theorem exponent_add_mul_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) = O.exponent (anchor + t)) :
    ∀ k t : ℕ,
      O.exponent (anchor + k * q + t) = O.exponent (anchor + t) := by
  intro k
  induction k with
  | zero =>
      intro t
      simp
  | succ k ih =>
      intro t
      calc
        O.exponent (anchor + (k + 1) * q + t)
            = O.exponent (anchor + (k * q + t) + q) := by
                congr 1
                simp only [Nat.succ_mul]
                omega
        _ = O.exponent (anchor + (k * q + t)) :=
          hperiod (k * q + t)
        _ = O.exponent (anchor + t) := by
          simpa only [Nat.add_assoc] using ih t

/-- 周期tailでは、`k`周期後の有限segmentが元の同位置segmentと一致する。 -/
theorem segment_add_mul_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) = O.exponent (anchor + t))
    (k t m : ℕ) :
    O.segment (anchor + k * q + t) m = O.segment (anchor + t) m := by
  induction m generalizing t with
  | zero =>
      simp
  | succ m ih =>
      simp only [segment_succ]
      rw [O.exponent_add_mul_period_eq hperiod k t]
      have htail := ih (t + 1)
      simpa [Nat.add_assoc] using htail

/-- 各周期境界から始まる一周期wordは同じword。 -/
theorem segment_mul_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) = O.exponent (anchor + t))
    (k : ℕ) :
    O.segment (anchor + k * q) q = O.segment anchor q := by
  simpa using O.segment_add_mul_period_eq hperiod k 0 q

/--
正のodd-only軌道上では、周期指数tailの一周期wordはexpandingになれない。

周期境界ごとの軌道値を取り出すと、同じ有限wordの無限反復実現になる。
-/
theorem no_expanding_periodic_exponent_tail
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) = O.exponent (anchor + t))
    (hExpanding : (O.segment anchor q).Expanding) :
    False := by
  let w : Collatz.Word := O.segment anchor q
  have hvalid : w.Valid := by
    simpa [w] using (O.runsSegment anchor q).valid
  apply hvalid.no_infiniteRepeatedRealization_of_expanding hExpanding
  refine ⟨fun k => O.value (anchor + k * q), ?_⟩
  intro k
  have hrun := O.realizesSegment (anchor + k * q) q
  have hword : O.segment (anchor + k * q) q = w := by
    simpa [w] using O.segment_mul_period_eq hperiod k
  rw [hword] at hrun
  have hend : anchor + k * q + q = anchor + (k + 1) * q := by
    ring
  simpa [hend] using hrun

end OddOrbit
end Collatz
