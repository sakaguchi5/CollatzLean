import CollatzLean.Collatz3.Canonical.AffineDataREQ
import CollatzLean.Collatz3.Core.WordTransfer
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: 無限指数列の canonical residue

正整数列 `e_0,e_1,...` の有限 prefix に対して、既存 affine-data residue をそのまま使う。
新しい modular solver は定義しない。

薄い座標は

* `prefixWord`
* `prefixDepth = D_m`
* `prefixAffine = A_m`
* `canonicalResidue = R_m`

だけ。

そこから

`A_(m+1) = 3 A_m + 2^D_m`

`R_(m+1) ≡ R_m (mod 2^(D_m+1))`

`R_(m+1) = R_m + 2^(D_m+1) q_m`, `q_m < 2^e_m`

を derived theorem として得る。
actual orbit semantics は使わない。
-/

namespace Collatz3
namespace IntegerReduction

/-- 無限指数列の先頭 `m` 文字。 -/
def prefixWord
    (e : ℕ → ℕ) : ℕ → Word
  | 0 => []
  | m + 1 => prefixWord e m ++ [e m]

/-- prefix の total 2-depth `D_m`。 -/
def prefixDepth
    (e : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  Word.twoSteps (prefixWord e m)

/-- prefix affine translation `A_m`。 -/
def prefixAffine
    (e : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  Word.affineConst (prefixWord e m)

/--
有限 prefix `(m,D_m,A_m)` が odd endpoint を持つための canonical start residue `R_m`。
正本は既存 `canonicalStartOfAffineData`。
-/
def canonicalResidue
    (e : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  canonicalStartOfAffineData
    m (prefixDepth e m) (prefixAffine e m)

@[simp] theorem prefixWord_zero
    (e : ℕ → ℕ) :
    prefixWord e 0 = [] := rfl

@[simp] theorem prefixWord_succ
    (e : ℕ → ℕ)
    (m : ℕ) :
    prefixWord e (m + 1) = prefixWord e m ++ [e m] := rfl

/-- prefix word の長さは index そのもの。 -/
theorem prefixWord_length
    (e : ℕ → ℕ)
    (m : ℕ) :
    (prefixWord e m).length = m := by
  induction m with
  | zero => simp [prefixWord]
  | succ m ih =>
      simp [prefixWord, ih]

/-- `D_(m+1)=D_m+e_m`。 -/
theorem prefixDepth_succ
    (e : ℕ → ℕ)
    (m : ℕ) :
    prefixDepth e (m + 1) = prefixDepth e m + e m := by
  simp [prefixDepth, prefixWord, Word.twoSteps]

/-- `A_(m+1)=3 A_m+2^D_m`。 -/
theorem prefixAffine_succ
    (e : ℕ → ℕ)
    (m : ℕ) :
    prefixAffine e (m + 1) =
      3 * prefixAffine e m + 2 ^ prefixDepth e m := by
  change
    Word.affineConst (prefixWord e m ++ [e m]) =
      3 * Word.affineConst (prefixWord e m) +
        2 ^ Word.twoSteps (prefixWord e m)
  rw [Word.affineConst_append]
  simp [Word.oddSteps, Word.twoSteps]

/-- `R_m` は法 `2^(D_m+1)` 未満。 -/
theorem canonicalResidue_lt_modulus
    (e : ℕ → ℕ)
    (m : ℕ) :
    canonicalResidue e m < 2 ^ (prefixDepth e m + 1) := by
  simpa [canonicalResidue] using
    canonicalStartOfAffineData_lt_modulus
      m (prefixDepth e m) (prefixAffine e m)

/--
canonical residue の defining congruence を `%` で書いた形。

`(3^m R_m + A_m) % 2^(D_m+1) = 2^D_m`。
-/
theorem canonicalResidue_mod
    (e : ℕ → ℕ)
    (m : ℕ) :
    (3 ^ m * canonicalResidue e m + prefixAffine e m) %
        2 ^ (prefixDepth e m + 1) =
      2 ^ prefixDepth e m := by
  simpa [
    canonicalResidue,
    canonicalNumeratorOfAffineData,
    oddEndpointModulusOfAffineData,
    Arithmetic.twoPowModulus
  ] using
    canonicalNumeratorOfAffineData_mod_modulus
      m (prefixDepth e m) (prefixAffine e m)

/-- defining congruence の `Nat.ModEq` 版。 -/
theorem canonicalResidue_modEq
    (e : ℕ → ℕ)
    (m : ℕ) :
    3 ^ m * canonicalResidue e m + prefixAffine e m ≡
      2 ^ prefixDepth e m
        [MOD 2 ^ (prefixDepth e m + 1)] := by
  change
    (3 ^ m * canonicalResidue e m + prefixAffine e m) %
        2 ^ (prefixDepth e m + 1) =
      (2 ^ prefixDepth e m) %
        2 ^ (prefixDepth e m + 1)
  rw [canonicalResidue_mod]
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  exact
    Nat.pow_lt_pow_right
      (by omega)
      (Nat.lt_succ_self _)

/--
指数が正なら、次の canonical residue は現在の residue と
`2^(D_m+1)` を法として同じ合同類にある。
-/
theorem canonicalResidue_succ_modEq
    (e : ℕ → ℕ)
    (hPos : ∀ m : ℕ, 0 < e m)
    (m : ℕ) :
    canonicalResidue e (m + 1) ≡ canonicalResidue e m
      [MOD 2 ^ (prefixDepth e m + 1)] := by
  let D := prefixDepth e m
  let D' := prefixDepth e (m + 1)
  let A := prefixAffine e m
  let R' := canonicalResidue e (m + 1)
  let M := 2 ^ (D + 1)
  have hD' : D' = D + e m := by
    dsimp [D, D']
    exact prefixDepth_succ e m
  have hDepthLe : D + 1 ≤ D' := by
    rw [hD']
    have := hPos m
    omega
  have hModulusDvd :
      M ∣ 2 ^ (D' + 1) := by
    dsimp [M]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hNext := canonicalResidue_modEq e (m + 1)
  have hNextSmall :
      3 ^ (m + 1) * R' + prefixAffine e (m + 1) ≡
        2 ^ D' [MOD M] := by
    dsimp [D', R', M]
    exact hNext.of_dvd hModulusDvd
  have hPowZero :
      2 ^ D' ≡ 0 [MOD M] := by
    change (2 ^ D') % M = 0 % M
    simp only [Nat.zero_mod]
    apply Nat.mod_eq_zero_of_dvd
    dsimp [M]
    exact Nat.pow_dvd_pow 2 hDepthLe
  have hNextZero :
      3 ^ (m + 1) * R' + prefixAffine e (m + 1) ≡
        0 [MOD M] :=
    hNextSmall.trans hPowZero
  have hNumerator :
      3 ^ (m + 1) * R' + prefixAffine e (m + 1) =
        3 * (3 ^ m * R' + A) + 2 ^ D := by
    dsimp [A, D]
    rw [prefixAffine_succ, pow_succ]
    ring
  rw [hNumerator] at hNextZero
  have hReferenceZero :
      3 * 2 ^ D + 2 ^ D ≡ 0 [MOD M] := by
    change (3 * 2 ^ D + 2 ^ D) % M = 0 % M
    simp only [Nat.zero_mod]
    apply Nat.mod_eq_zero_of_dvd
    have hEq : 3 * 2 ^ D + 2 ^ D = 2 ^ (D + 2) := by
      rw [pow_add]
      norm_num
      ring
    rw [hEq]
    dsimp [M]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hSum :
      3 * (3 ^ m * R' + A) + 2 ^ D ≡
        3 * 2 ^ D + 2 ^ D [MOD M] :=
    hNextZero.trans hReferenceZero.symm
  have hMul :
      3 * (3 ^ m * R' + A) ≡
        3 * 2 ^ D [MOD M] :=
    Nat.ModEq.add_right_cancel' (2 ^ D) hSum
  have hCoprimeThree : Nat.Coprime M 3 := by
    dsimp [M]
    simpa using
      (Arithmetic.coprime_threePow_twoPow 1 (D + 1)).symm
  have hPrefixNumerator :
      3 ^ m * R' + A ≡ 2 ^ D [MOD M] :=
    Nat.ModEq.cancel_left_of_coprime
      hCoprimeThree.gcd_eq_one hMul
  have hCurrent := canonicalResidue_modEq e m
  have hCurrent' :
      3 ^ m * canonicalResidue e m + A ≡
        2 ^ D [MOD M] := by
    simpa [A, D, M] using hCurrent
  have hSameNumerator :
      3 ^ m * R' + A ≡
        3 ^ m * canonicalResidue e m + A [MOD M] :=
    hPrefixNumerator.trans hCurrent'.symm
  have hSameMul :
      3 ^ m * R' ≡
        3 ^ m * canonicalResidue e m [MOD M] :=
    Nat.ModEq.add_right_cancel' A hSameNumerator
  have hCoprimePower : Nat.Coprime M (3 ^ m) := by
    dsimp [M]
    exact (Arithmetic.coprime_threePow_twoPow m (D + 1)).symm
  have hResidue :
      R' ≡ canonicalResidue e m [MOD M] :=
    Nat.ModEq.cancel_left_of_coprime
      hCoprimePower.gcd_eq_one hSameMul
  simpa [R', M] using hResidue

/--
positive exponent 列では一段 lift digit `q_m` が存在し、

`R_(m+1) = R_m + 2^(D_m+1) q_m`, `q_m < 2^e_m`。
-/
theorem exists_canonicalResidue_liftDigit
    (e : ℕ → ℕ)
    (hPos : ∀ m : ℕ, 0 < e m)
    (m : ℕ) :
    ∃ q : ℕ,
      q < 2 ^ e m ∧
      canonicalResidue e (m + 1) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * q := by
  let M := 2 ^ (prefixDepth e m + 1)
  let R := canonicalResidue e m
  let R' := canonicalResidue e (m + 1)
  have hCong := canonicalResidue_succ_modEq e hPos m
  have hRlt : R < M := by
    dsimp [R, M]
    exact canonicalResidue_lt_modulus e m
  have hMod : R' % M = R := by
    change R' % M = R % M at hCong
    rw [Nat.mod_eq_of_lt hRlt] at hCong
    exact hCong
  let q := R' / M
  have hDecomp := Nat.mod_add_div R' M
  rw [hMod] at hDecomp
  have hEq : R' = R + M * q := by
    dsimp [q]
    exact hDecomp.symm
  have hNextLt := canonicalResidue_lt_modulus e (m + 1)
  have hDepth := prefixDepth_succ e m
  have hUpperEq :
      2 ^ (prefixDepth e (m + 1) + 1) =
        M * 2 ^ e m := by
    dsimp [M]
    rw [hDepth]
    rw [show prefixDepth e m + e m + 1 =
          (prefixDepth e m + 1) + e m by omega,
      pow_add]
  rw [hUpperEq] at hNextLt
  have hMqLe : M * q ≤ R' := by
    rw [hEq]
    omega
  have hMqLt : M * q < M * 2 ^ e m :=
    lt_of_le_of_lt hMqLe hNextLt
  have hq : q < 2 ^ e m :=
    Nat.lt_of_mul_lt_mul_left hMqLt
  refine ⟨q, hq, ?_⟩
  simpa [R, R', M] using hEq

/-- lift digit の表示は一意。 -/
theorem canonicalResidue_liftDigit_unique
    (e : ℕ → ℕ)
    (m q₁ q₂ : ℕ)
    (h₁ :
      canonicalResidue e (m + 1) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * q₁)
    (h₂ :
      canonicalResidue e (m + 1) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * q₂) :
    q₁ = q₂ := by
  have hMul :
      2 ^ (prefixDepth e m + 1) * q₁ =
        2 ^ (prefixDepth e m + 1) * q₂ := by
    omega
  exact
    Nat.mul_left_cancel
      (Arithmetic.twoPow_pos (prefixDepth e m + 1))
      hMul

/-- positive exponent 列では canonical residue は非減少。 -/
theorem canonicalResidue_le_succ
    (e : ℕ → ℕ)
    (hPos : ∀ m : ℕ, 0 < e m)
    (m : ℕ) :
    canonicalResidue e m ≤ canonicalResidue e (m + 1) := by
  rcases exists_canonicalResidue_liftDigit e hPos m with ⟨q, _hq, hEq⟩
  rw [hEq]
  omega

end IntegerReduction
end Collatz3
