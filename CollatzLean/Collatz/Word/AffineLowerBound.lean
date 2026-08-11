import CollatzLean.Collatz.Word.Basic

/-!
# valid finite word の affine lower bound

forward affine decoder の途中で残る tail は、実在する valid word なら
その長さだけで決まる普遍的な affine lower bound を満たす。

長さ `m` の valid word では

  `3^m - 2^m <= affineConst`

である。decoder の任意段階の residual は、元の word の `drop` tail の
affine constant なので同じ bound を満たす。
-/

namespace Collatz
namespace Word

/-- valid 性は任意の drop tail に保存される。 -/
theorem Valid.drop
    {w : Collatz.Word}
    (h : Valid w) (k : ℕ) :
    Valid (w.drop k) := by
  intro e he
  apply h e
  have hdecomp : w.take k ++ w.drop k = w :=
    List.take_append_drop k w
  rw [← hdecomp]
  exact List.mem_append.mpr (Or.inr he)

/--
valid word の affine constant に対する加法形 lower bound。
subtraction を避けた形を基本定理にする。
-/
theorem Valid.threePow_le_affineConst_add_twoPow
    {w : Collatz.Word}
    (h : Valid w) :
    3 ^ oddSteps w ≤ affineConst w + 2 ^ oddSteps w := by
  induction w with
  | nil =>
      simp [oddSteps, affineConst]
  | cons e w ih =>
      have he : 0 < e := h e (by simp)
      have htail : Valid w := by
        intro a ha
        exact h a (by simp [ha])
      have hi := ih htail
      have htwo : 2 ≤ 2 ^ e := by
        have hpow : 2 ^ 1 ≤ 2 ^ e :=
          Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) he
        simpa using hpow
      have hB :
          2 * affineConst w ≤ 2 ^ e * affineConst w := by
        exact Nat.mul_le_mul_right (affineConst w) htwo
      have hiScaled :
          2 * 3 ^ oddSteps w ≤
            2 * affineConst w + 2 * 2 ^ oddSteps w := by
        have hmul := Nat.mul_le_mul_left 2 hi
        simpa [Nat.mul_add] using hmul
      calc
        3 ^ oddSteps (e :: w)
            = 3 ^ oddSteps w + 2 * 3 ^ oddSteps w := by
                simp only [oddSteps_cons, pow_succ]
                ring
        _ ≤ 3 ^ oddSteps w +
              (2 * affineConst w + 2 * 2 ^ oddSteps w) :=
          Nat.add_le_add_left hiScaled _
        _ ≤ 3 ^ oddSteps w +
              (2 ^ e * affineConst w + 2 * 2 ^ oddSteps w) := by
          omega
        _ = affineConst (e :: w) + 2 ^ oddSteps (e :: w) := by
          simp only [affineConst_cons, oddSteps_cons, pow_succ]
          ring

/-- valid 長さ `m` の word では `affineConst >= 3^m - 2^m`。 -/
theorem Valid.threePow_sub_twoPow_le_affineConst
    {w : Collatz.Word}
    (h : Valid w) :
    3 ^ oddSteps w - 2 ^ oddSteps w ≤ affineConst w := by
  have hmain := h.threePow_le_affineConst_add_twoPow
  omega

/--
decoder の任意段階の residual tail も同じ普遍 lower bound を満たす。
`w.drop k` が、その段階でまだ復元されていない residual word に対応する。
-/
theorem Valid.decoderResidual_lowerBound
    {w : Collatz.Word}
    (h : Valid w) (k : ℕ) :
    3 ^ oddSteps (w.drop k) - 2 ^ oddSteps (w.drop k) ≤
      affineConst (w.drop k) := by
  exact (h.drop k).threePow_sub_twoPow_le_affineConst

/--
valid residual が lower bound を割れば、その residual を持つ word は存在しない。
forward decoder の停止 certificate として使う。
-/
theorem no_valid_word_of_affineConst_lt_minimum
    {w : Collatz.Word}
    (hsmall : affineConst w < 3 ^ oddSteps w - 2 ^ oddSteps w) :
    ¬ Valid w := by
  intro hvalid
  have hmin := hvalid.threePow_sub_twoPow_le_affineConst
  omega

end Word
end Collatz
