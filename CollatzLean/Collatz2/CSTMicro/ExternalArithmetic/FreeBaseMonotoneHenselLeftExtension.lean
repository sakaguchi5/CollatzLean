import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselRepeatArithmetic
import Mathlib.Data.Nat.Prime.Int

/-!
# Free-base Hensel repeat: 左延長と 3-adic unit の同値

repeated block の現在位置で

  delta j = delta i + Delta

が成立しているとする。ひとつ左の qOne recurrence を二本引き算すると、
入口 scaled difference

  E = Q_j - 2^Delta Q_i

について、

  3 ∣ E

であることと、predecessor でも同じ exponent offset が成立することが同値になる。

この補題は「左へ maximal に延長してそこで止まる」ことを、
scaled difference が mod 3 で unit であるという exact arithmetic certificate に変換する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/-- 3 は任意の 2 冪を割らない。mixed predecessor case の排除に使う。 -/
private theorem three_not_dvd_twoPow (n : ℕ) :
    ¬ (3 : ℤ) ∣ (2 : ℤ) ^ n := by
  intro h
  have hTwo : (3 : ℤ) ∣ (2 : ℤ) :=
    Int.prime_three.dvd_of_dvd_pow h
  norm_num at hTwo

/--
ひとつ左の二本の qOne recurrence を、同じ `2^Delta` scaling で差し引いた exact relation。
-/
theorem predecessor_scaledDifference_relation
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta : ℕ}
    (hiPos : 0 < i)
    (hjPos : 0 < j)
    (hi : i < C.width)
    (hj : j < C.width) :
    3 * C.scaledDifference (i - 1) (j - 1) Delta 0 =
      2 * C.scaledDifference i j Delta 0 +
        (2 : ℤ) ^ C.delta (j - 1) -
        (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) := by
  have hiPrev : i - 1 < C.width := by omega
  have hjPrev : j - 1 < C.width := by omega
  have hLeft := C.qOne_recurrence (i := i - 1) hiPrev
  have hRight := C.qOne_recurrence (i := j - 1) hjPrev
  have hiIdx : i - 1 + 1 = i := by omega
  have hjIdx : j - 1 + 1 = j := by omega
  rw [hiIdx] at hLeft
  rw [hjIdx] at hRight
  have hLeftScaled :=
    congrArg
      (fun z : ℤ => (2 : ℤ) ^ Delta * z)
      hLeft
  unfold scaledDifference
  simp only [Nat.add_zero]
  ring_nf at hLeftScaled hRight ⊢
  linarith

/--
現在位置で exponent offset が `Delta` なら、

  3 ∣ scaledDifference i j Delta 0

と「同じ offset で一セル左へ延長できる」ことは同値。

proof の本質は predecessor step の4ケースである。
両方 stay / 両方 rise なら左延長でき、mixed case では差に非零の 2 冪が一つ残るため
mod 3 divisibility と両立しない。
-/
theorem three_dvd_scaledDifference_zero_iff_leftExtendable
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta : ℕ}
    (hiPos : 0 < i)
    (hjPos : 0 < j)
    (hi : i < C.width)
    (hj : j < C.width)
    (hDelta : C.delta j = C.delta i + Delta) :
    (3 : ℤ) ∣ C.scaledDifference i j Delta 0 ↔
      C.delta (j - 1) = C.delta (i - 1) + Delta := by
  have hPred :=
    C.predecessor_scaledDifference_relation
      (i := i) (j := j) (Delta := Delta)
      hiPos hjPos hi hj
  have hStepI := C.delta_step (i - 1) (by omega)
  have hStepJ := C.delta_step (j - 1) (by omega)
  have hiIdx : i - 1 + 1 = i := by omega
  have hjIdx : j - 1 + 1 = j := by omega
  rw [hiIdx] at hStepI
  rw [hjIdx] at hStepJ
  constructor
  · intro hThree
    rcases hThree with ⟨u, hu⟩
    rcases hStepI with hISame | hIUp
    · rcases hStepJ with hJSame | hJUp
      · omega
      · have hExp :
            Delta + C.delta (i - 1) =
              C.delta (j - 1) + 1 := by
          omega
        have hPow :
            (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) =
              2 * (2 : ℤ) ^ C.delta (j - 1) := by
          calc
            (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1)
                = (2 : ℤ) ^ (Delta + C.delta (i - 1)) := by
                    rw [pow_add]
            _ = (2 : ℤ) ^ (C.delta (j - 1) + 1) := by rw [hExp]
            _ = (2 : ℤ) ^ C.delta (j - 1) * 2 := by rw [pow_succ]
            _ = 2 * (2 : ℤ) ^ C.delta (j - 1) := by ring
        have hDvdPow :
            (3 : ℤ) ∣ (2 : ℤ) ^ C.delta (j - 1) := by
          refine ⟨2 * u - C.scaledDifference (i - 1) (j - 1) Delta 0, ?_⟩
          rw [hu, hPow] at hPred
          linarith
        exact False.elim ((three_not_dvd_twoPow (C.delta (j - 1))) hDvdPow)
    · rcases hStepJ with hJSame | hJUp
      · have hExp :
            C.delta (j - 1) =
              Delta + C.delta (i - 1) + 1 := by
          omega
        have hPowBase :
            (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) =
              (2 : ℤ) ^ (Delta + C.delta (i - 1)) := by
          rw [pow_add]
        have hPowRight :
            (2 : ℤ) ^ C.delta (j - 1) =
              2 * ((2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1)) := by
          calc
            (2 : ℤ) ^ C.delta (j - 1)
                = (2 : ℤ) ^ (Delta + C.delta (i - 1) + 1) := by rw [hExp]
            _ = (2 : ℤ) ^ (Delta + C.delta (i - 1)) * 2 := by rw [pow_succ]
            _ = 2 * ((2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1)) := by
                  rw [← hPowBase]
                  ring
        have hDvdPow :
            (3 : ℤ) ∣ (2 : ℤ) ^ (Delta + C.delta (i - 1)) := by
          refine ⟨C.scaledDifference (i - 1) (j - 1) Delta 0 - 2 * u, ?_⟩
          rw [hu, hPowRight, hPowBase] at hPred
          linarith
        exact False.elim
          ((three_not_dvd_twoPow (Delta + C.delta (i - 1))) hDvdPow)
      · omega
  · intro hLeft
    have hPow :
        (2 : ℤ) ^ C.delta (j - 1) =
          (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) := by
      rw [hLeft, pow_add]
      ring
    rw [hPow] at hPred
    have hDivTwo :
        (3 : ℤ) ∣ 2 * C.scaledDifference i j Delta 0 := by
      refine ⟨C.scaledDifference (i - 1) (j - 1) Delta 0, ?_⟩
      linarith
    have hCoprime : IsCoprime (3 : ℤ) (2 : ℤ) := by
      refine ⟨1, -1, ?_⟩
      norm_num
    exact hCoprime.dvd_of_dvd_mul_left hDivTwo

/--
左へ一セル延長できない repeated block の入口 scaled difference は mod 3 unit。
maximal-left stop からそのまま使う convenience corollary。
-/
theorem three_not_dvd_scaledDifference_zero_of_not_leftExtendable
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta : ℕ}
    (hiPos : 0 < i)
    (hjPos : 0 < j)
    (hi : i < C.width)
    (hj : j < C.width)
    (hDelta : C.delta j = C.delta i + Delta)
    (hStop : C.delta (j - 1) ≠ C.delta (i - 1) + Delta) :
    ¬ (3 : ℤ) ∣ C.scaledDifference i j Delta 0 := by
  intro hThree
  exact hStop
    ((C.three_dvd_scaledDifference_zero_iff_leftExtendable
      hiPos hjPos hi hj hDelta).1 hThree)

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
