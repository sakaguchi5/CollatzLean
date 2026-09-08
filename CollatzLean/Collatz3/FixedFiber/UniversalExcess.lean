import CollatzLean.Collatz3.Core.WordTransfer

/-!
# Collatz3: fixed-fiber universal excess

固定 `p` の基準 translation

`3^p - 2^p`

からの差を fixed-fiber excess `E_RF` として扱う。
ここでは RecordFerrers を定義・仮定しない。
将来、RecordFerrers を導入した後に幾何的な面積座標として解釈できる形を保つ。

符号を失わない `signedFixedFiberBaseline : ℕ → ℤ` と
`signedUniversalExcess : Word → ℤ` を数学的な正本とする。

従来の `fixedFiberBaseline : ℕ → ℕ` と `universalExcess : Word → ℕ` は、
valid word 上で使う互換用 Nat view として残す。
-/

namespace Collatz3
namespace Word

/-- fixed odd-step count `p` に対する Nat-valued 基準 translation。 -/
def fixedFiberBaseline (p : ℕ) : ℕ :=
  3 ^ p - 2 ^ p

/--
符号を失わない fixed-fiber baseline。

`3^p - 2^p` を最初から整数差として持つ。
-/
def signedFixedFiberBaseline (p : ℕ) : ℤ :=
  (3 : ℤ) ^ p - (2 : ℤ) ^ p

/-- signed baseline は Nat baseline の exact cast。 -/
theorem signedFixedFiberBaseline_eq_natCast
    (p : ℕ) :
    signedFixedFiberBaseline p =
      (fixedFiberBaseline p : ℤ) := by
  have hPow : 2 ^ p ≤ 3 ^ p := by
    exact Nat.pow_le_pow_left (by decide : 2 ≤ (3 : ℕ)) _
  unfold signedFixedFiberBaseline fixedFiberBaseline
  rw [Nat.cast_sub hPow]
  simp

/--
Nat baseline の 1 段再帰。

`D_(q+1) = 3^q + 2*D_q`
-/
theorem fixedFiberBaseline_succ (q : ℕ) :
    fixedFiberBaseline (q + 1) =
      3 ^ q + 2 * fixedFiberBaseline q := by
  have hPow : 2 ^ q ≤ 3 ^ q := by
    exact Nat.pow_le_pow_left (by decide : 2 ≤ (3 : ℕ)) _
  unfold fixedFiberBaseline
  rw [pow_succ, pow_succ]
  omega

/--
signed baseline の 1 段再帰。

`D_(q+1) = 3^q + 2*D_q`
-/
theorem signedFixedFiberBaseline_succ (q : ℕ) :
    signedFixedFiberBaseline (q + 1) =
      (3 : ℤ) ^ q + 2 * signedFixedFiberBaseline q := by
  unfold signedFixedFiberBaseline
  rw [pow_succ, pow_succ]
  ring

/--
符号を失わない fixed-fiber excess `E_RF`。
raw Word に対しても情報を潰さない。
RecordFerrers に依存しない算術的な正本として定義する。
-/
def signedUniversalExcess (w : Word) : ℤ :=
  (affineConst w : ℤ) -
    signedFixedFiberBaseline (oddSteps w)

/--
従来互換の Nat-valued excess。
valid word では baseline 以下に落ちないので signed 版と一致する。
-/
def universalExcess (w : Word) : ℕ :=
  affineConst w - fixedFiberBaseline (oddSteps w)

/-- 正指数 `e` では `2 ≤ 2^e`。 -/
theorem two_le_twoPow_of_pos
    {e : ℕ}
    (he : 0 < e) :
    2 ≤ 2 ^ e := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
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
        exact
          Nat.pow_le_pow_left
            (by decide : 2 ≤ (3 : ℕ)) _
      omega

/-- valid word では signed `E_RF` は非負。 -/
theorem signedUniversalExcess_nonneg
    {w : Word}
    (hValid : Valid w) :
    0 ≤ signedUniversalExcess w := by
  have hBase :=
    fixedFiberBaseline_le_affineConst hValid
  unfold signedUniversalExcess
  rw [signedFixedFiberBaseline_eq_natCast]
  omega

/-- valid word では Nat view は signed `E_RF` の exact cast。 -/
theorem signedUniversalExcess_eq_natCast
    {w : Word}
    (hValid : Valid w) :
    signedUniversalExcess w =
      (universalExcess w : ℤ) := by
  have hBase :=
    fixedFiberBaseline_le_affineConst hValid
  unfold signedUniversalExcess universalExcess
  rw [signedFixedFiberBaseline_eq_natCast]
  rw [Nat.cast_sub hBase]

/-- valid word では `B = baseline + E_RF` が exact に復元される。 -/
theorem affineConst_eq_fixedFiberBaseline_add_universalExcess
    {w : Word}
    (hValid : Valid w) :
    affineConst w =
      fixedFiberBaseline (oddSteps w) + universalExcess w := by
  unfold universalExcess
  simpa [Nat.add_comm] using
    (Nat.sub_add_cancel
      (fixedFiberBaseline_le_affineConst hValid)).symm

/-- signed `E_RF` からも `B` を exact に復元できる。 -/
theorem affineConst_int_eq_fixedFiberBaseline_add_signedUniversalExcess
    {w : Word} :
    (affineConst w : ℤ) =
      (fixedFiberBaseline (oddSteps w) : ℤ) +
        signedUniversalExcess w := by
  unfold signedUniversalExcess
  rw [signedFixedFiberBaseline_eq_natCast]
  ring

/-- fixed `p` では Nat `E_RF` が affine translation を識別する。 -/
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

/-- fixed `p` では signed `E_RF` も affine translation を識別する。 -/
theorem affineConst_eq_of_same_oddSteps_and_signedUniversalExcess
    {u v : Word}
    (hp : oddSteps u = oddSteps v)
    (hE : signedUniversalExcess u = signedUniversalExcess v) :
    affineConst u = affineConst v := by
  unfold signedUniversalExcess at hE
  rw [hp] at hE
  omega

end Word
end Collatz3
