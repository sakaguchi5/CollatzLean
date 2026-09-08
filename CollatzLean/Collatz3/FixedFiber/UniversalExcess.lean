import CollatzLean.Collatz3.Core.WordTransfer

/-!
# Collatz3: fixed-fiber universal excess

固定 `(p,H)` の中で affine translation `B` を

  B = (3^p - 2^p) + E_RF

と分解するための薄い view。
`E_RF` は新しい primitive data ではなく `affineConst` から導く。
-/

namespace Collatz3
namespace Word

/-- fixed odd-step count `p` に対する基準 translation。 -/
def fixedFiberBaseline (p : ℕ) : ℕ :=
  3 ^ p - 2 ^ p

/-- RecordFerrers / fixed-fiber の universal excess `E_RF`。 -/
def universalExcess (w : Word) : ℕ :=
  affineConst w - fixedFiberBaseline (oddSteps w)

/-- 正指数 `e` では `2 ≤ 2^e`。 -/
theorem two_le_twoPow_of_pos
    {e : ℕ}
    (he : 0 < e) :
    2 ≤ 2 ^ e := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [pow_succ]
  have hp : 0 < 2 ^ d := Nat.pow_pos (by decide)
  omega

/-- valid word の affine translation は fixed-fiber baseline 以上。 -/
theorem fixedFiberBaseline_le_affineConst
    {w : Word}
    (hValid : Valid w) :
    fixedFiberBaseline (oddSteps w) ≤ affineConst w := by
  induction w with
  | nil =>
      simp [fixedFiberBaseline, affineConst]
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      have hIH := ih hTail
      have hTwo : 2 ≤ 2 ^ e := two_le_twoPow_of_pos he
      have hMul :
          2 * fixedFiberBaseline (oddSteps tail) ≤
            2 ^ e * affineConst tail := by
        exact le_trans
          (Nat.mul_le_mul_left 2 hIH)
          (Nat.mul_le_mul hTwo (Nat.le_refl (affineConst tail)))
      unfold fixedFiberBaseline at hMul ⊢
      rw [oddSteps_cons, affineConst_cons, pow_succ, pow_succ]
      have h3pow : 2 ^ oddSteps tail ≤ 3 ^ oddSteps tail := by
        exact Nat.pow_le_pow_left (by decide : 2 ≤ (3 : ℕ)) _
      omega

/-- valid word では `B = baseline + E_RF` が exact に復元される。 -/
theorem affineConst_eq_fixedFiberBaseline_add_universalExcess
    {w : Word}
    (hValid : Valid w) :
    affineConst w =
      fixedFiberBaseline (oddSteps w) + universalExcess w := by
  unfold universalExcess
  simpa [Nat.add_comm] using
    (Nat.sub_add_cancel (fixedFiberBaseline_le_affineConst hValid)).symm

/-- fixed `p` では `E_RF` が affine translation を識別する。 -/
theorem affineConst_eq_of_same_oddSteps_and_universalExcess
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hp : oddSteps u = oddSteps v)
    (hE : universalExcess u = universalExcess v) :
    affineConst u = affineConst v := by
  rw [affineConst_eq_fixedFiberBaseline_add_universalExcess hu]
  rw [affineConst_eq_fixedFiberBaseline_add_universalExcess hv]
  rw [hp, hE]

end Word
end Collatz3
