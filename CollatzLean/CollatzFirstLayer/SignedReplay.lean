import CollatzLean.CollatzFirstLayer.CanonicalReplay
import CollatzLean.CollatzFirstLayer.DownwardReplay

import Mathlib.Tactic.Linarith

/-!
# short positive-shadow terminalの排除

自然数上のactual runをcanonical replay幅だけ整数方向へ一段下げる。
開始値が負なら各odd-only stepは負値を負値へ送るため、終点側の
predecessor shadowも必ず負になる。

したがって、canonical terminalでpredecessor shadowが正になる
short positive-shadow枝は存在しない。
-/

namespace CollatzFirstLayer
namespace ExpWord
namespace Runs

/--
actual runを整数方向へ`k`段下げたとき、下げた開始値が負なら
対応する下げた終点も負である。

中間値を明示的な型として保存せず、自然数runに沿った帰納で符号だけを輸送する。
-/
theorem signedReplay_finish_neg
    {w : ExpWord} {X Y : ℕ}
    (h : Runs w X Y)
    (k : ℤ)
    (hk : 0 < k)
    (hstart :
      (X : ℤ) - (residueModulus w : ℤ) * k < 0) :
    (Y : ℤ) -
        2 * (3 : ℤ) ^ oddSteps w * k < 0 := by
  induction h generalizing k with
  | nil x =>
      simpa [residueModulus, twoSteps, oddSteps] using hstart
  | @cons e w x y z he hstep hy htail ih =>
      have hstepZ :
          (2 : ℤ) ^ e * (y : ℤ) =
            3 * (x : ℤ) + 1 := by
        exact_mod_cast hstep
      have hmodulus :
          (residueModulus (e :: w) : ℤ) =
            (2 : ℤ) ^ e * (residueModulus w : ℤ) := by
        exact_mod_cast (residueModulus_cons_eq e w)
      have hshiftedStep :
          (2 : ℤ) ^ e *
              ((y : ℤ) - (residueModulus w : ℤ) * (3 * k)) =
            3 *
                ((x : ℤ) -
                  (residueModulus (e :: w) : ℤ) * k) +
              1 := by
        calc
          (2 : ℤ) ^ e *
                ((y : ℤ) - (residueModulus w : ℤ) * (3 * k))
              =
            (2 : ℤ) ^ e * (y : ℤ) -
              3 *
                ((2 : ℤ) ^ e *
                  (residueModulus w : ℤ) * k) := by
                    ring
          _ =
            (3 * (x : ℤ) + 1) -
              3 *
                ((2 : ℤ) ^ e *
                  (residueModulus w : ℤ) * k) := by
                    rw [hstepZ]
          _ =
            3 *
                ((x : ℤ) -
                  (residueModulus (e :: w) : ℤ) * k) +
              1 := by
                    rw [hmodulus]
                    ring
      have hshiftedStart_le :
          (x : ℤ) -
              (residueModulus (e :: w) : ℤ) * k ≤ -1 := by
        omega
      have hrightNeg :
          3 *
                ((x : ℤ) -
                  (residueModulus (e :: w) : ℤ) * k) +
              1 < 0 := by
        omega
      have hproductNeg :
          (2 : ℤ) ^ e *
              ((y : ℤ) - (residueModulus w : ℤ) * (3 * k)) < 0 := by
        rw [hshiftedStep]
        exact hrightNeg
      have hpowPos : 0 < (2 : ℤ) ^ e := by
        positivity
      have hmiddleNeg :
          (y : ℤ) - (residueModulus w : ℤ) * (3 * k) < 0 := by
        by_contra hnot
        have hmiddleNonneg :
            0 ≤ (y : ℤ) - (residueModulus w : ℤ) * (3 * k) :=
          le_of_not_gt hnot
        have hproductNonneg :
            0 ≤ (2 : ℤ) ^ e *
              ((y : ℤ) - (residueModulus w : ℤ) * (3 * k)) :=
          mul_nonneg hpowPos.le hmiddleNonneg
        exact (not_lt_of_ge hproductNonneg) hproductNeg
      have hkTail : 0 < 3 * k := by
        nlinarith
      have htailNeg := ih (3 * k) hkTail hmiddleNeg
      have hwidth :
          2 * (3 : ℤ) ^ oddSteps (e :: w) * k =
            2 * (3 : ℤ) ^ oddSteps w * (3 * k) := by
        simp only [oddSteps_cons, pow_succ]
        ring
      rw [hwidth]
      exact htailNeg

/--
canonical開始値からcanonical終点へactualに走れる語では、
一段下のpredecessor shadowは必ず負。
-/
theorem predecessorShadow_neg_of_canonical_run
    {w : ExpWord}
    (h : Runs w (canonicalStart w) (canonicalEnd w)) :
    predecessorShadow w < 0 := by
  have hstart :
      (canonicalStart w : ℤ) -
          (residueModulus w : ℤ) * (1 : ℤ) < 0 := by
    simpa [predecessorStart] using predecessorStart_neg w
  have hfinish :=
    signedReplay_finish_neg h (1 : ℤ) (by norm_num) hstart
  simpa [predecessorShadow] using hfinish

end Runs
end ExpWord
end CollatzFirstLayer
