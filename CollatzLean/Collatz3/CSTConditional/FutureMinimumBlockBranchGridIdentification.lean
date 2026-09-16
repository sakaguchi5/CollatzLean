import CollatzLean.Collatz3.CSTConditional.FutureMinimumDyadicGridBlockTransport
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: block branch digit と dyadic-grid digit の同一化

Stage 6 では completion block branch digit `J` を一意化し、Stage 7 では
future-minimum defect-grid 分子 `Z` の block transport

`3^j (Z_i - 2^H Z_j) ≡ C (mod 2^δ)`

を得た。

ここでは `H ≤ δ` の通常 block について、この二つの整数自由度が同じものであることを示す。

同じ current `Z_i` と correction `C` に対する二つの next grid 候補 `Z₁,Z₂` は
transport congruence の差から

`Z₂ = Z₁ + 2^(δ-H) k`

と書ける。
next defect が `δ+a` (`a=0/1`) なので、dyadic state の定義から

`tau₂ - tau₁ = 4k / 2^(H+a)`。

一方 block branch recurrence の差は

`4(J₂-J₁) = 2^(H+a)(tau₂-tau₁)`。

従って exact に

`J₂-J₁ = k`。

つまり completion block branch digit と、`Z_j` に残る高位 grid digit は同一の整数自由度である。
actual compatibility を両候補に課せば Stage 6 の branch uniqueness により `k=0` となり、
next grid 候補も一意になる。

新しい digit 関数・state structure は導入しない。
-/

namespace Collatz3
namespace Bridge

/--
同じ block transport congruence を満たす二つの next-grid 候補の差。

`H ≤ δ` なら `Z₂-Z₁` は `2^(δ-H)` の倍数。
-/
theorem dyadicGrid_blockTransport_candidates_spacing
    (j δ H : ℕ)
    (Zi Z₁ Z₂ C : ℤ)
    (hH : H ≤ δ)
    (h₁ :
      (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Z₁) ≡
        C [ZMOD (2 : ℤ) ^ δ])
    (h₂ :
      (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Z₂) ≡
        C [ZMOD (2 : ℤ) ^ δ]) :
    ∃ k : ℤ,
      Z₂ = Z₁ + (2 : ℤ) ^ (δ - H) * k := by
  have hBoth :
      (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Z₁) ≡
        (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Z₂)
        [ZMOD (2 : ℤ) ^ δ] :=
    h₁.trans h₂.symm
  have hCancel :
      Zi - (2 : ℤ) ^ H * Z₁ ≡
        Zi - (2 : ℤ) ^ H * Z₂
        [ZMOD (2 : ℤ) ^ δ] :=
    cancel_threePow_modEq_lattice hBoth
  rcases Int.modEq_iff_add_fac.mp hCancel with ⟨q, hq⟩
  have hPow :
      (2 : ℤ) ^ δ =
        (2 : ℤ) ^ H * (2 : ℤ) ^ (δ - H) := by
    rw [← pow_add]
    congr 1
    omega
  have hMul :
      (2 : ℤ) ^ H * (Z₁ - Z₂) =
        (2 : ℤ) ^ H * ((2 : ℤ) ^ (δ - H) * q) := by
    calc
      (2 : ℤ) ^ H * (Z₁ - Z₂)
          = (2 : ℤ) ^ δ * q := by
              linear_combination hq
      _ = (2 : ℤ) ^ H * ((2 : ℤ) ^ (δ - H) * q) := by
              rw [hPow]
              ring
  have hPowNe : (2 : ℤ) ^ H ≠ 0 := by
    exact pow_ne_zero H (by norm_num)
  have hDiff :
      Z₁ - Z₂ = (2 : ℤ) ^ (δ - H) * q :=
    mul_left_cancel₀ hPowNe hMul
  refine ⟨-q, ?_⟩
  linear_combination -hDiff

/--
`Z₂ = Z₁ + 2^(δ-H)k` と dyadic-grid 表現から、normalized lift の差を読む。

next defect が `D=δ+a` なら
`2^(H+a)(tau₂-tau₁)=4k`。
-/
theorem dyadicGrid_spacing_implies_scaledLiftDifference
    (δ H a D : ℕ)
    (hH : H ≤ δ)
    (hD : D = δ + a)
    (sigma tau₁ tau₂ : ℝ)
    (Z₁ Z₂ k : ℤ)
    (hGrid₁ :
      (tau₁ - 2 + 3 * sigma) / 4 =
        (Z₁ : ℝ) / (2 : ℝ) ^ D)
    (hGrid₂ :
      (tau₂ - 2 + 3 * sigma) / 4 =
        (Z₂ : ℝ) / (2 : ℝ) ^ D)
    (hZ :
      Z₂ = Z₁ + (2 : ℤ) ^ (δ - H) * k) :
    (2 : ℝ) ^ (H + a) * (tau₂ - tau₁) = 4 * (k : ℝ) := by
  have hDiff :
      (tau₂ - tau₁) / 4 =
        ((Z₂ : ℝ) - (Z₁ : ℝ)) / (2 : ℝ) ^ D := by
    linear_combination hGrid₂ - hGrid₁
  have hZR :
      (Z₂ : ℝ) - (Z₁ : ℝ) =
        (2 : ℝ) ^ (δ - H) * (k : ℝ) := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at hz
    linarith
  have hPow :
      (2 : ℝ) ^ D =
        (2 : ℝ) ^ (δ - H) * (2 : ℝ) ^ (H + a) := by
    rw [hD]
    rw [← pow_add]
    congr 1
    omega
  rw [hZR, hPow] at hDiff
  have hA : (0 : ℝ) < (2 : ℝ) ^ (δ - H) := by positivity
  have hS : (0 : ℝ) < (2 : ℝ) ^ (H + a) := by positivity
  have hFrac :
      ((2 : ℝ) ^ (δ - H) * (k : ℝ)) /
          ((2 : ℝ) ^ (δ - H) * (2 : ℝ) ^ (H + a)) =
        (k : ℝ) / (2 : ℝ) ^ (H + a) := by
    field_simp
  rw [hFrac] at hDiff
  have hMul := (eq_div_iff hS.ne').mp hDiff
  nlinarith [hMul]

/--
block recurrence と dyadic-grid spacing を同時に満たすと、branch digit 差は grid digit `k` に一致。
-/
theorem normalizedBlockBranchDifference_eq_dyadicGridDigit
    (δ H a D : ℕ)
    (hH : H ≤ δ)
    (hD : D = δ + a)
    (tauCurrent rho sigma tau₁ tau₂ : ℝ)
    (J₁ J₂ Z₁ Z₂ k : ℤ)
    (hRec₁ :
      rho + 4 * (J₁ : ℝ) =
        (2 : ℝ) ^ (H + a) * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (J₂ : ℝ) =
        (2 : ℝ) ^ (H + a) * tau₂ - tauCurrent)
    (hGrid₁ :
      (tau₁ - 2 + 3 * sigma) / 4 =
        (Z₁ : ℝ) / (2 : ℝ) ^ D)
    (hGrid₂ :
      (tau₂ - 2 + 3 * sigma) / 4 =
        (Z₂ : ℝ) / (2 : ℝ) ^ D)
    (hZ :
      Z₂ = Z₁ + (2 : ℤ) ^ (δ - H) * k) :
    J₂ - J₁ = k := by
  have hLift :=
    dyadicGrid_spacing_implies_scaledLiftDifference
      δ H a D hH hD sigma tau₁ tau₂ Z₁ Z₂ k hGrid₁ hGrid₂ hZ
  have hRecDiff :
      (2 : ℝ) ^ (H + a) * (tau₂ - tau₁) =
        4 * (((J₂ - J₁ : ℤ) : ℝ)) := by
    push_cast
    linarith [hRec₁, hRec₂]
  have hEqR :
      (((J₂ - J₁ : ℤ) : ℝ)) = (k : ℝ) := by
    nlinarith [hLift, hRecDiff]
  exact_mod_cast hEqR

end Bridge

namespace OddOrbit

open Bridge
open CSTConditional

/--
next-future-minimum block で二つの transport-compatible grid 候補を比較する package。

`H ≤ δ_i` ならある整数 `k` が存在し、

* `Z₂ = Z₁ + 2^(δ_i-H) k`,
* `J₂-J₁ = k`

が同時に成り立つ。
-/
theorem exists_blockGridDigit_eq_branchDifference_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hH :
      Critical.beattyIndex (j - i) ≤
        infiniteSurvivorDefect O.exponent i)
    (Zi Z₁ Z₂ C J₁ J₂ : ℤ)
    (tauCurrent rho tau₁ tau₂ : ℝ)
    (hTransport₁ :
      (3 : ℤ) ^ j *
          (Zi - (2 : ℤ) ^ Critical.beattyIndex (j - i) * Z₁) ≡
        C [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i])
    (hTransport₂ :
      (3 : ℤ) ^ j *
          (Zi - (2 : ℤ) ^ Critical.beattyIndex (j - i) * Z₂) ≡
        C [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i])
    (hRec₁ :
      rho + 4 * (J₁ : ℝ) =
        (2 : ℝ) ^
            (Critical.beattyIndex (j - i) +
              Critical.beattyCarry i (j - i)) * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (J₂ : ℝ) =
        (2 : ℝ) ^
            (Critical.beattyIndex (j - i) +
              Critical.beattyCarry i (j - i)) * tau₂ - tauCurrent)
    (hGrid₁ :
      (tau₁ - 2 +
          3 * centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j)) / 4 =
        (Z₁ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent j)
    (hGrid₂ :
      (tau₂ - 2 +
          3 * centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j)) / 4 =
        (Z₂ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent j) :
    ∃ k : ℤ,
      Z₂ = Z₁ +
          (2 : ℤ) ^
            (infiniteSurvivorDefect O.exponent i -
              Critical.beattyIndex (j - i)) * k ∧
      J₂ - J₁ = k := by
  let δ := infiniteSurvivorDefect O.exponent i
  let H := Critical.beattyIndex (j - i)
  let a := Critical.beattyCarry i (j - i)
  have hDef :=
    O.nextFutureMinimum_defect_eq_add_carry_of_globalCST
      G SInf hStart hNext
  rcases
      Bridge.dyadicGrid_blockTransport_candidates_spacing
        j δ H Zi Z₁ Z₂ C (by simpa [δ, H] using hH)
        hTransport₁ hTransport₂ with ⟨k, hZ⟩
  have hJ :=
    Bridge.normalizedBlockBranchDifference_eq_dyadicGridDigit
      δ H a (infiniteSurvivorDefect O.exponent j)
      (by simpa [δ, H] using hH)
      (by simpa [δ, a] using hDef)
      tauCurrent rho
      (centeredNormalizedCompletionCocycleResidue
        j (infiniteSurvivorDefect O.exponent j))
      tau₁ tau₂ J₁ J₂ Z₁ Z₂ k
      hRec₁ hRec₂ hGrid₁ hGrid₂ hZ
  exact ⟨k, by simpa [δ, H] using hZ, hJ⟩

/--
前定理に actual finite compatibility を加えた elimination theorem。

両候補が actual-compatible なら Stage 6 により `J₁=J₂`、従って `k=0` で
`Z₁=Z₂`。`H ≤ δ_i` の block では next dyadic-grid branch の自由度が消える。
-/
theorem actualCompatible_nextDyadicGridCandidate_unique_of_beattyIndex_le_defect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hH :
      Critical.beattyIndex (j - i) ≤
        infiniteSurvivorDefect O.exponent i)
    (Zi Z₁ Z₂ C J₁ J₂ z₁ z₂ : ℤ)
    (tauCurrent rho tau₁ tau₂ : ℝ)
    (hTransport₁ :
      (3 : ℤ) ^ j *
          (Zi - (2 : ℤ) ^ Critical.beattyIndex (j - i) * Z₁) ≡
        C [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i])
    (hTransport₂ :
      (3 : ℤ) ^ j *
          (Zi - (2 : ℤ) ^ Critical.beattyIndex (j - i) * Z₂) ≡
        C [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i])
    (hRec₁ :
      rho + 4 * (J₁ : ℝ) =
        (2 : ℝ) ^
            (Critical.beattyIndex (j - i) +
              Critical.beattyCarry i (j - i)) * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (J₂ : ℝ) =
        (2 : ℝ) ^
            (Critical.beattyIndex (j - i) +
              Critical.beattyCarry i (j - i)) * tau₂ - tauCurrent)
    (hTau₁ : 0 < tau₁ ∧ tau₁ < 4)
    (hTau₂ : 0 < tau₂ ∧ tau₂ < 4)
    (hCompat₁ :
      O.defectActualResidueFraction j +
          ((3 : ℝ) ^ j / 4) * (tau₁ - 2) = (z₁ : ℝ))
    (hCompat₂ :
      O.defectActualResidueFraction j +
          ((3 : ℝ) ^ j / 4) * (tau₂ - 2) = (z₂ : ℝ))
    (hGrid₁ :
      (tau₁ - 2 +
          3 * centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j)) / 4 =
        (Z₁ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent j)
    (hGrid₂ :
      (tau₂ - 2 +
          3 * centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j)) / 4 =
        (Z₂ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent j) :
    Z₁ = Z₂ := by
  rcases
      O.exists_blockGridDigit_eq_branchDifference_of_globalCST
        G SInf hStart hNext hH
        Zi Z₁ Z₂ C J₁ J₂ tauCurrent rho tau₁ tau₂
        hTransport₁ hTransport₂ hRec₁ hRec₂ hGrid₁ hGrid₂ with
    ⟨k, hZ, hJ⟩
  have hBranch : J₁ = J₂ :=
    Bridge.actualCompatible_normalizedCompletionBlockBranchDigit_unique
      j
      (Critical.beattyIndex (j - i) + Critical.beattyCarry i (j - i))
      tauCurrent rho tau₁ tau₂
      (O.defectActualResidueFraction j)
      J₁ J₂ z₁ z₂
      hRec₁ hRec₂ hTau₁ hTau₂ hCompat₁ hCompat₂
  have hk : k = 0 := by omega
  rw [hk] at hZ
  simp at hZ
  exact hZ.symm

end OddOrbit
end Collatz3
