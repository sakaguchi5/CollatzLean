import CollatzLean.CollatzSecondLayer2.InfiniteOrbit
import CollatzLean.CollatzFirstLayer.PeriodicAffine
import Mathlib.Tactic.Ring

/-!
# 周期指数tailの有限語反復への還元

指数tailが周期`q`を持つなら、周期境界ごとの各`q`-segmentは同じ有限指数語である。
したがって、その一周期語が膨張する場合は、第一層の有限アフィン反復排除定理に反する。

このファイルは無限軌道固有の薄い適用層だけを担当する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/--
指数tailが`q`周期なら、`k`周期後の各指数は元の指数と一致する。
-/
theorem exponent_add_mul_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t)) :
    ∀ k t : ℕ,
      O.exponent (anchor + k * q + t) =
        O.exponent (anchor + t) := by
  intro k
  induction k with
  | zero =>
      intro t
      simp
  | succ k ih =>
      intro t
      calc
        O.exponent (anchor + (k + 1) * q + t)
            =
          O.exponent (anchor + (k * q + t) + q) := by
            congr 1
            simp only [Nat.succ_mul]
            omega
        _ =
          O.exponent (anchor + (k * q + t)) :=
            hperiod (k * q + t)
        _ =
          O.exponent (anchor + t) := by
            simpa only [Nat.add_assoc] using ih t

/--
周期tailでは、`k`周期後の任意の有限segmentが元の同位置segmentと一致する。
-/
theorem segmentWord_add_mul_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t))
    (k t m : ℕ) :
    O.segmentWord (anchor + k * q + t) m =
      O.segmentWord (anchor + t) m := by
  induction m generalizing t with
  | zero =>
      simp
  | succ m ih =>
      simp only [segmentWord_succ]
      rw [O.exponent_add_mul_period_eq hperiod k t]
      have htail := ih (t + 1)
      simpa [Nat.add_assoc] using htail

/-- 各周期境界から始まる一周期語は同じ語。 -/
theorem segmentWord_mul_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t))
    (k : ℕ) :
    O.segmentWord (anchor + k * q) q =
      O.segmentWord anchor q := by
  simpa using
    O.segmentWord_add_mul_period_eq hperiod k 0 q

/--
正のodd-only軌道上では、周期指数tailの一周期語は膨張できない。

周期境界ごとの軌道値を取り出すと、同じ有限語の無限反復実現になるため、
第一層の`no_infiniteRepeatedRealization_of_valid_expanding`に反する。
-/
theorem no_expanding_periodic_exponent_tail
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t))
    (hexpanding : Expanding (O.segmentWord anchor q)) :
    False := by
  let w : ExpWord := O.segmentWord anchor q
  have hvalid : Valid w := by
    simpa [w] using (O.runs_segment anchor q).valid
  apply
    (no_infiniteRepeatedRealization_of_valid_expanding
      hvalid hexpanding)
  refine ⟨fun k => O.value (anchor + k * q), ?_⟩
  intro k
  have hrun := O.realizes_segment (anchor + k * q) q
  have hword :
      O.segmentWord (anchor + k * q) q = w := by
    simpa [w] using O.segmentWord_mul_period_eq hperiod k
  rw [hword] at hrun
  have hend :
      anchor + k * q + q = anchor + (k + 1) * q := by
    ring
  simpa [hend] using hrun

end OddOrbit
end CollatzSecondLayer2
