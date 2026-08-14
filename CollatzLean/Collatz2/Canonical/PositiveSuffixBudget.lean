import CollatzLean.Collatz2.Canonical.EndpointFundamentalBound
import CollatzLean.Collatz2.Local.TranslationDeterminant
import CollatzLean.Collatz2.Geometry.Center

/-!
# Collatz2 Canonical: positive all-suffix-contracting budget

FirstCrossing を仮定せず、

* valid / nonempty
* all nonempty suffixes contracting
* canonical start < canonical end

だけから positive canonical return の sharp budget を取り出す。

canonical half-gap を `n`、whole center gap を `G`、
`A = 2^H` とすると exact に

  B = G*S + 2*A*n

であり、suffix determinant integral の strict negativity

  3*B < p*A

から

  3*G*S + 6*n*A < p*A
  6*n < p

が従う。

さらに `sigma = p - 6*n` と suffix excess

  K = p*A - 3*B

を使うと

  sigma*A = 3*G*S + K

という exact budget identity になる。
-/

namespace Collatz2
namespace Word

/-- all-suffix-contracting な nonempty word 自身も contracting。 -/
theorem AllSuffixesContracting.whole_contracting
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    Contracting w := by
  have hlen : 0 < w.length :=
    List.length_pos_iff.mpr hne
  have h0 := hAll 0 hlen
  simpa [
    suffixDeterminant,
    Contracting,
    AffineTransfer.NegativeDeterminant
  ] using h0

/--
Suffix determinant budget の natural excess。
all-suffix-contracting nonempty word では正になる。
-/
def suffixBudgetExcess (w : Word) : ℕ :=
  oddSteps w * 2 ^ twoSteps w - 3 * affineConst w

/-- all-suffix-contracting nonempty word の suffix budget excess は正。 -/
theorem AllSuffixesContracting.suffixBudgetExcess_pos
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    0 < suffixBudgetExcess w := by
  have h :=
    hAll.three_mul_affineConst_lt_oddSteps_mul_twoPow hne
  unfold suffixBudgetExcess
  exact Nat.sub_pos_of_lt h

/--
`suffixBudgetExcess` は signed suffix determinant integral の符号を反転した natural shadow。

  (K : ℤ) = - suffixDeterminantIntegral w
-/
theorem AllSuffixesContracting.suffixBudgetExcess_int_eq_neg_integral
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    (suffixBudgetExcess w : ℤ) = -suffixDeterminantIntegral w := by
  have hlt :=
    hAll.three_mul_affineConst_lt_oddSteps_mul_twoPow hne
  have hle :
      3 * affineConst w ≤ oddSteps w * 2 ^ twoSteps w :=
    Nat.le_of_lt hlt
  have hNat :
      3 * affineConst w + suffixBudgetExcess w =
        oddSteps w * 2 ^ twoSteps w := by
    unfold suffixBudgetExcess
    omega
  have hZ :
      (3 : ℤ) * (affineConst w : ℤ) +
          (suffixBudgetExcess w : ℤ) =
        (oddSteps w : ℤ) * ((2 : ℤ) ^ twoSteps w) := by
    exact_mod_cast hNat
  rw [suffixDeterminantIntegral_eq]
  linarith

/--
canonical positive return の half-gap と exact affine balance。

`G = 2^H - 3^p` を `centerGap` として保持し、Nat subtraction を外へ露出しない。
-/
theorem AllSuffixesContracting.exists_canonicalHalfGap_and_exactBalance
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hvalid : Valid w)
    (hne : w ≠ [])
    (hpos : canonicalStart w < canonicalEnd w) :
    ∃ n : ℕ,
      0 < n ∧
      canonicalEnd w = canonicalStart w + 2 * n ∧
      affineConst w =
        (AffineTransfer.ofWord w).centerGap * canonicalStart w +
          2 ^ (twoSteps w + 1) * n := by
  have hstartOdd : Odd (canonicalStart w) :=
    canonicalStart_odd_of_valid_nonempty hvalid hne
  have hendOdd : Odd (canonicalEnd w) := canonicalEnd_odd w
  rcases hstartOdd with ⟨a, ha⟩
  rcases hendOdd with ⟨b, hb⟩
  have hab : a < b := by omega
  let n := b - a
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  have hreturn :
      canonicalEnd w = canonicalStart w + 2 * n := by
    dsimp [n]
    omega
  have hC : Contracting w := hAll.whole_contracting hne
  have hneg : (AffineTransfer.ofWord w).determinant < 0 := hC
  have hle :
      (AffineTransfer.ofWord w).oddCoeff ≤
        (AffineTransfer.ofWord w).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hgapCoeff :
      (AffineTransfer.ofWord w).centerGap +
          (AffineTransfer.ofWord w).oddCoeff =
        (AffineTransfer.ofWord w).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hle
  have hgap :
      (AffineTransfer.ofWord w).centerGap + 3 ^ oddSteps w =
        2 ^ twoSteps w := by
    simpa using hgapCoeff
  have hreal :=
    (realizes_iff w (canonicalStart w) (canonicalEnd w)).1
      (canonicalEnd_realizes w)
  have hsum :
      3 ^ oddSteps w * canonicalStart w +
          ((AffineTransfer.ofWord w).centerGap * canonicalStart w +
            2 ^ (twoSteps w + 1) * n) =
        3 ^ oddSteps w * canonicalStart w + affineConst w := by
    calc
      3 ^ oddSteps w * canonicalStart w +
          ((AffineTransfer.ofWord w).centerGap * canonicalStart w +
            2 ^ (twoSteps w + 1) * n)
          =
        (3 ^ oddSteps w +
            (AffineTransfer.ofWord w).centerGap) * canonicalStart w +
          2 * 2 ^ twoSteps w * n := by
            rw [pow_succ]
            ring
      _ =
        2 ^ twoSteps w * canonicalStart w +
          2 * 2 ^ twoSteps w * n := by
            rw [Nat.add_comm
              (3 ^ oddSteps w)
              (AffineTransfer.ofWord w).centerGap,
              hgap]
      _ =
        2 ^ twoSteps w *
          (canonicalStart w + 2 * n) := by ring
      _ = 2 ^ twoSteps w * canonicalEnd w := by rw [← hreturn]
      _ = 3 ^ oddSteps w * canonicalStart w + affineConst w := hreal
  have hexact :
      affineConst w =
        (AffineTransfer.ofWord w).centerGap * canonicalStart w +
          2 ^ (twoSteps w + 1) * n := by
    exact (Nat.add_left_cancel hsum).symm
  exact ⟨n, hnPos, hreturn, hexact⟩

/--
canonical positive all-suffix-contracting word の sharp budget。
FirstCrossing の prefix profile は使わない。
-/
theorem AllSuffixesContracting.exists_canonicalHalfGap_and_budget
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hvalid : Valid w)
    (hne : w ≠ [])
    (hpos : canonicalStart w < canonicalEnd w) :
    ∃ n : ℕ,
      0 < n ∧
      canonicalEnd w = canonicalStart w + 2 * n ∧
      3 * (AffineTransfer.ofWord w).centerGap * canonicalStart w +
          6 * n * 2 ^ twoSteps w <
        oddSteps w * 2 ^ twoSteps w := by
  obtain ⟨n, hnPos, hreturn, hbalance⟩ :=
    hAll.exists_canonicalHalfGap_and_exactBalance hvalid hne hpos
  have hB :=
    hAll.three_mul_affineConst_lt_oddSteps_mul_twoPow hne
  rw [hbalance] at hB
  rw [pow_succ] at hB
  have hbudget :
      3 * (AffineTransfer.ofWord w).centerGap * canonicalStart w +
          6 * n * 2 ^ twoSteps w <
        oddSteps w * 2 ^ twoSteps w := by
    nlinarith
  exact ⟨n, hnPos, hreturn, hbudget⟩

/-- canonical positive all-suffix-contracting word では `6*n < p`。 -/
theorem AllSuffixesContracting.exists_canonicalHalfGap_six_lt_oddSteps
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hvalid : Valid w)
    (hne : w ≠ [])
    (hpos : canonicalStart w < canonicalEnd w) :
    ∃ n : ℕ,
      0 < n ∧
      canonicalEnd w = canonicalStart w + 2 * n ∧
      6 * n < oddSteps w := by
  obtain ⟨n, hnPos, hreturn, hbudget⟩ :=
    hAll.exists_canonicalHalfGap_and_budget hvalid hne hpos
  have hpowPos : 0 < 2 ^ twoSteps w := Nat.pow_pos (by omega)
  have hscaled :
      (6 * n) * 2 ^ twoSteps w <
        oddSteps w * 2 ^ twoSteps w := by
    have hle :
        (6 * n) * 2 ^ twoSteps w ≤
          3 * (AffineTransfer.ofWord w).centerGap * canonicalStart w +
            6 * n * 2 ^ twoSteps w := by
      omega
    exact lt_of_le_of_lt hle hbudget
  have hsix : 6 * n < oddSteps w := by
    exact (Nat.mul_lt_mul_right hpowPos).mp hscaled
  exact ⟨n, hnPos, hreturn, hsix⟩

/--
`p = 6*n + sigma` と suffix excess `K` による exact budget identity。

  sigma * 2^H = 3*G*S + K

ここで `K = suffixBudgetExcess w > 0`。
-/
theorem AllSuffixesContracting.exists_canonicalHalfGap_sigma_budgetIdentity
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hvalid : Valid w)
    (hne : w ≠ [])
    (hpos : canonicalStart w < canonicalEnd w) :
    ∃ n sigma : ℕ,
      0 < n ∧
      0 < sigma ∧
      canonicalEnd w = canonicalStart w + 2 * n ∧
      oddSteps w = 6 * n + sigma ∧
      sigma * 2 ^ twoSteps w =
        3 * (AffineTransfer.ofWord w).centerGap * canonicalStart w +
          suffixBudgetExcess w := by
  obtain ⟨n, hnPos, hreturn, hbalance⟩ :=
    hAll.exists_canonicalHalfGap_and_exactBalance hvalid hne hpos
  obtain ⟨_n, _hnPos, _hreturn, hsix⟩ :=
    hAll.exists_canonicalHalfGap_six_lt_oddSteps hvalid hne hpos
  have hnEq : _n = n := by
    omega
  subst _n
  let sigma := oddSteps w - 6 * n
  have hsigmaPos : 0 < sigma := by
    dsimp [sigma]
    omega
  have hp : oddSteps w = 6 * n + sigma := by
    dsimp [sigma]
    omega
  have hBlt :=
    hAll.three_mul_affineConst_lt_oddSteps_mul_twoPow hne
  have hBle :
      3 * affineConst w ≤ oddSteps w * 2 ^ twoSteps w :=
    Nat.le_of_lt hBlt
  have hExcessAdd :
      3 * affineConst w + suffixBudgetExcess w =
        oddSteps w * 2 ^ twoSteps w := by
    unfold suffixBudgetExcess
    omega
  have hidentity :
      sigma * 2 ^ twoSteps w =
        3 * (AffineTransfer.ofWord w).centerGap * canonicalStart w +
          suffixBudgetExcess w := by
    rw [hbalance, pow_succ] at hExcessAdd
    rw [hp] at hExcessAdd
    ring_nf at hExcessAdd
    nlinarith
  exact ⟨n, sigma, hnPos, hsigmaPos, hreturn, hp, hidentity⟩

end Word
end Collatz2
