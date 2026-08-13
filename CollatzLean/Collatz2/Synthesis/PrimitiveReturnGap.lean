import CollatzLean.Collatz2.Synthesis.GlobalPrimitiveCenter

/-!
# Collatz2 Synthesis: primitive return-gap coordinates

negative future-minimum block の actual return gap を center content で primitive 化する。
新しい branch data は導入しない。

`h = gcd(returnGap, G)`、`G = h*d`、`returnGap = 4*h*s` として
primitive return-gap `s` を導き、`gcd(s,d)=1` を得る。
さらに primitive center coordinate `alpha` と `s` を接続し、
隣接 primitive separation `kappa` を

  `kappa = d*A'*s' - d'*C*s`

へ exact に戻す。
-/

namespace Collatz2
namespace Synthesis

namespace AdjacentTransferChain

/-- content を除き、さらに future-minimum gap の共通因子 `4` を除いた primitive return gap。 -/
def primitiveReturnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (returnGap C n / centerContent C n) / 4

/--
negative block で start future minimum が `>1` なら
actual return gap は exact に `4*h*s`。
-/
theorem returnGap_eq_four_mul_content_mul_primitiveReturnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    returnGap C n =
      4 * centerContent C n * primitiveReturnGap C n := by
  let h := centerContent C n
  let t := returnGap C n / h
  have hhgap : h ∣ returnGap C n := centerContent_dvd_returnGap C hN
  have hht : h * t = returnGap C n := by
    simpa [h, t] using Nat.mul_div_cancel' hhgap
  have hstartMin : 1 < O.value (C.minima.index n) := by
    simpa [AdjacentTransferChain.startValue,
      AdjacentTransferChain.startIndex] using hstart
  obtain ⟨q, _hqpos, hgap4⟩ := C.minima.valueGap_eq_four_mul hstartMin
  have hreturn4 : returnGap C n = 4 * q := by
    simpa [returnGap, OddOrbit.FutureMinima.valueGap,
      AdjacentTransferChain.startValue,
      AdjacentTransferChain.endValue,
      AdjacentTransferChain.startIndex,
      AdjacentTransferChain.endIndex] using hgap4
  have hfourDivProd : 4 ∣ h * t := by
    rw [hht, hreturn4]
    exact ⟨q, rfl⟩
  have hcop4h : Nat.Coprime 4 h := by
    simpa [h] using four_coprime_centerContent C hN
  have hfourDivT : 4 ∣ t :=
    hcop4h.dvd_of_dvd_mul_left hfourDivProd
  have hfourMul : 4 * (t / 4) = t :=
    Nat.mul_div_cancel' hfourDivT
  unfold primitiveReturnGap
  change returnGap C n = 4 * h * (t / 4)
  calc
    returnGap C n = h * t := hht.symm
    _ = h * (4 * (t / 4)) := by
      rw [hfourMul]
    _ = 4 * h * (t / 4) := by
      ring

/--
`returnGap / h` と `G / h` は coprime。
`h = gcd(returnGap,G)` の直接の primitive 化。
-/
theorem returnGap_div_content_coprime_denominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime
      (returnGap C n / centerContent C n)
      (primitiveCenterDenominator C n) := by
  have hG : 0 < centerGap (C.transfer n) := by
    have hneg : (C.transfer n).determinant < 0 := by
      simpa [AdjacentTransferChain.NegativeAt,
        AffineTransfer.NegativeDeterminant] using hN
    exact centerGap_pos_of_negative hneg
  have hgcd :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right
      (n := returnGap C n)
      (m := centerGap (C.transfer n))
      hG
  rw [← centerContent_eq_returnGap_gcd C hN] at hgcd
  simpa [primitiveCenterDenominator, Nat.Coprime] using hgcd

/-- primitive return gap `s` と primitive denominator `d` は coprime。 -/
theorem primitiveReturnGap_coprime_denominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    Nat.Coprime
      (primitiveReturnGap C n)
      (primitiveCenterDenominator C n) := by
  have hcop := returnGap_div_content_coprime_denominator C hN
  have hEq :=
    returnGap_eq_four_mul_content_mul_primitiveReturnGap C hN hstart
  have hhpos : 0 < centerContent C n := centerContent_pos C hN
  have hdiv :
      returnGap C n / centerContent C n = 4 * primitiveReturnGap C n := by
    have hmul :
        returnGap C n =
          centerContent C n * (4 * primitiveReturnGap C n) := by
      rw [hEq]
      ring
    exact Nat.div_eq_of_eq_mul_right hhpos hmul
  have hsdiv :
      primitiveReturnGap C n ∣
        returnGap C n / centerContent C n := by
    rw [hdiv]
    exact dvd_mul_left _ _
  exact hcop.of_dvd_left hsdiv

/-- negative block の natural spectral gap `G=A-C` は odd。 -/
theorem centerGap_odd_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Odd (centerGap (C.transfer n)) := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  have hCA : (C.transfer n).oddCoeff < (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hHpos : 0 < Word.twoSteps (C.word n) :=
    Word.twoSteps_pos_of_valid_nonempty (C.word_valid n) (C.word_nonempty n)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (C.transfer n).twoCoeff = 2 * a := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Word.twoSteps (C.word n) = k + 1 := by
      exact ⟨Word.twoSteps (C.word n) - 1, by omega⟩
    refine ⟨2 ^ k, ?_⟩
    change 2 ^ Word.twoSteps (C.word n) = 2 * 2 ^ k
    rw [hk, pow_succ]
    ring
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (C.transfer n).oddCoeff = 2 * b + 1 := by
    change ∃ b : ℕ, 3 ^ Word.oddSteps (C.word n) = 2 * b + 1
    induction Word.oddSteps (C.word n) with
    | zero => exact ⟨0, by simp⟩
    | succ p ih =>
        rcases ih with ⟨b, hb⟩
        refine ⟨3 * b + 1, ?_⟩
        rw [pow_succ, hb]
        ring
  refine ⟨a - b - 1, ?_⟩
  unfold centerGap
  rw [ha, hb]
  omega

/-- center content `h` 自体も odd。 -/
theorem centerContent_odd_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Odd (centerContent C n) := by
  have hGodd := centerGap_odd_of_negativeAt C hN
  have hfac :=
    centerContent_mul_primitiveCenterDenominator C n
  rw [← hfac] at hGodd
  exact Nat.Odd.of_mul_left hGodd

/-- primitive center denominator `d` も odd。 -/
theorem primitiveCenterDenominator_odd_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Odd (primitiveCenterDenominator C n) := by
  have hGodd := centerGap_odd_of_negativeAt C hN
  have hfac :=
    centerContent_mul_primitiveCenterDenominator C n
  rw [← hfac] at hGodd
  exact Nat.Odd.of_mul_right hGodd

/--
start future minimum `x=4m+3` を使うと
`alpha = d*m + A*s`。
-/
theorem primitiveAlpha_eq_start_coordinate
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    ∃ m : ℕ,
      C.startValue n = 4 * m + 3 ∧
      primitiveAlpha C n =
        primitiveCenterDenominator C n * m +
          (C.transfer n).twoCoeff * primitiveReturnGap C n := by
  have hstartMin : 1 < O.value (C.startIndex n) := by
    simpa [AdjacentTransferChain.startValue] using hstart
  obtain ⟨m, hm⟩ :=
    (C.startFutureMinimum n).value_eq_four_mul_add_three hstartMin
  have hmStart :
      C.startValue n = 4 * m + 3 := by
    simpa [AdjacentTransferChain.startValue] using hm
  have hGap :=
    returnGap_eq_four_mul_content_mul_primitiveReturnGap C hN hstart
  have hB :=
    translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap C hN
  have hhb :=
    centerContent_mul_primitiveCenterNumerator C n
  have hhd :=
    centerContent_mul_primitiveCenterDenominator C n
  have hhpos : 0 < centerContent C n := centerContent_pos C hN
  let q :=
    primitiveCenterDenominator C n * m +
      (C.transfer n).twoCoeff * primitiveReturnGap C n
  have hbq :
      primitiveCenterNumerator C n =
        3 * primitiveCenterDenominator C n + 4 * q := by
    have hcancel :
      centerContent C n * primitiveCenterNumerator C n =
        centerContent C n *
          (3 * primitiveCenterDenominator C n + 4 * q) := by
      calc
      centerContent C n * primitiveCenterNumerator C n
          = (C.transfer n).translate := hhb
      _ = centerGap (C.transfer n) * C.startValue n +
            (C.transfer n).twoCoeff * returnGap C n := hB
      _ =
          (centerContent C n * primitiveCenterDenominator C n) *
              (4 * m + 3) +
            (C.transfer n).twoCoeff *
              (4 * centerContent C n * primitiveReturnGap C n) := by
        rw [← hhd, hmStart, hGap]
      _ = centerContent C n *
            (3 * primitiveCenterDenominator C n + 4 * q) := by
        dsimp [q]
        ring
    exact Nat.mul_left_cancel hhpos hcancel
  have hnormal := (primitiveCenter_normal_form C hN hstart).1
  have halpha : primitiveAlpha C n = q := by
    omega
  exact ⟨m, by simpa [AdjacentTransferChain.startValue] using hm,
    by simpa [q] using halpha⟩

/--
endpoint future minimum `y=4m+3` を使うと
`alpha = d*m + C*s`。
-/
theorem primitiveAlpha_eq_end_coordinate
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    ∃ m : ℕ,
      C.endValue n = 4 * m + 3 ∧
      primitiveAlpha C n =
        primitiveCenterDenominator C n * m +
          (C.transfer n).oddCoeff * primitiveReturnGap C n := by
  have hend : 1 < C.endValue n := by
    exact lt_trans hstart (C.startValue_lt_endValue n)
  obtain ⟨m, hm⟩ :=
    (C.endFutureMinimum n).value_eq_four_mul_add_three hend
  have hmEnd :
      C.endValue n = 4 * m + 3 := by
    simpa [AdjacentTransferChain.endValue] using hm
  have hGap :=
    returnGap_eq_four_mul_content_mul_primitiveReturnGap C hN hstart
  have hB := translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap C hN
  have hhb := centerContent_mul_primitiveCenterNumerator C n
  have hhd := centerContent_mul_primitiveCenterDenominator C n
  have hhpos : 0 < centerContent C n := centerContent_pos C hN
  let q :=
    primitiveCenterDenominator C n * m +
      (C.transfer n).oddCoeff * primitiveReturnGap C n
  have hbq :
      primitiveCenterNumerator C n =
        3 * primitiveCenterDenominator C n + 4 * q := by
    have hcancel :
        centerContent C n * primitiveCenterNumerator C n =
          centerContent C n *
            (3 * primitiveCenterDenominator C n + 4 * q) := by
      calc
        centerContent C n * primitiveCenterNumerator C n
            = (C.transfer n).translate := hhb
        _ = centerGap (C.transfer n) * C.endValue n +
              (C.transfer n).oddCoeff * returnGap C n := hB
        _ =
            (centerContent C n * primitiveCenterDenominator C n) *
                (4 * m + 3) +
              (C.transfer n).oddCoeff *
                (4 * centerContent C n * primitiveReturnGap C n) := by
          rw [← hhd, hmEnd, hGap]
        _ = centerContent C n *
              (3 * primitiveCenterDenominator C n + 4 * q) := by
          dsimp [q]
          ring
    exact Nat.mul_left_cancel hhpos hcancel
  have hnormal := (primitiveCenter_normal_form C hN hstart).1
  have halpha : primitiveAlpha C n = q := by
    omega
  exact ⟨m, by simpa [AdjacentTransferChain.endValue] using hm,
    by simpa [q] using halpha⟩

/--
隣接 primitive separation を return-gap 座標へ完全に戻した exact identity。

`kappa = d*A'*s' - d'*C*s`。
-/
theorem primitiveKappa_eq_gap_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    primitiveKappa C n =
      (primitiveCenterDenominator C n : ℤ) *
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
          (primitiveReturnGap C (n + 1) : ℤ) -
        (primitiveCenterDenominator C (n + 1) : ℤ) *
          ((C.transfer n).oddCoeff : ℤ) *
          (primitiveReturnGap C n : ℤ) := by
  have hstartNext : 1 < C.startValue (n + 1) := by
    rw [← endValue_eq_next_startValue C n]
    exact lt_trans hstart (C.startValue_lt_endValue n)
  have hGapN :=
    returnGap_eq_four_mul_content_mul_primitiveReturnGap C hN hstart
  have hGapNs :=
    returnGap_eq_four_mul_content_mul_primitiveReturnGap C hNs hstartNext
  have hGn := centerContent_mul_primitiveCenterDenominator C n
  have hGns := centerContent_mul_primitiveCenterDenominator C (n + 1)
  have hBal := omegaAdjacent_eq_returnGap_balance C hN hNs
  have hFac :=
    omegaAdjacent_eq_four_mul_contents_mul_primitiveKappa C hN hNs hstart
  have hGapNZ :
      (returnGap C n : ℤ) =
        4 * (centerContent C n : ℤ) *
          (primitiveReturnGap C n : ℤ) := by
    exact_mod_cast hGapN
  have hGapNsZ :
      (returnGap C (n + 1) : ℤ) =
        4 * (centerContent C (n + 1) : ℤ) *
          (primitiveReturnGap C (n + 1) : ℤ) := by
    exact_mod_cast hGapNs
  have hGnZ :
      (centerGap (C.transfer n) : ℤ) =
        (centerContent C n : ℤ) *
          (primitiveCenterDenominator C n : ℤ) := by
    exact_mod_cast hGn.symm
  have hGnsZ :
      (centerGap (C.transfer (n + 1)) : ℤ) =
        (centerContent C (n + 1) : ℤ) *
          (primitiveCenterDenominator C (n + 1) : ℤ) := by
    exact_mod_cast hGns.symm
  let R : ℤ :=
    (primitiveCenterDenominator C n : ℤ) *
        ((C.transfer (n + 1)).twoCoeff : ℤ) *
        (primitiveReturnGap C (n + 1) : ℤ) -
      (primitiveCenterDenominator C (n + 1) : ℤ) *
        ((C.transfer n).oddCoeff : ℤ) *
        (primitiveReturnGap C n : ℤ)
  have hBal' :
      omegaAdjacent C n =
        4 * (centerContent C n : ℤ) *
          (centerContent C (n + 1) : ℤ) * R := by
    rw [hBal, hGnZ, hGnsZ, hGapNZ, hGapNsZ]
    dsimp [R]
    ring
  have hcoef :
      (4 : ℤ) * (centerContent C n : ℤ) *
        (centerContent C (n + 1) : ℤ) ≠ 0 := by
    have hn := centerContent_pos C hN
    have hns := centerContent_pos C hNs
    positivity
  have heq :
      (4 : ℤ) * (centerContent C n : ℤ) *
          (centerContent C (n + 1) : ℤ) * primitiveKappa C n =
        (4 : ℤ) * (centerContent C n : ℤ) *
          (centerContent C (n + 1) : ℤ) * R := by
    rw [← hFac, ← hBal']
  have hcancel := mul_left_cancel₀ hcoef heq
  simpa [R] using hcancel

/-- word coefficients を展開した `2^H / 3^p` 形。 -/
theorem primitiveKappa_eq_twoPow_threePow_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    primitiveKappa C n =
      (primitiveCenterDenominator C n : ℤ) *
          ((2 ^ Word.twoSteps (C.word (n + 1)) : ℕ) : ℤ) *
          (primitiveReturnGap C (n + 1) : ℤ) -
        (primitiveCenterDenominator C (n + 1) : ℤ) *
          ((3 ^ Word.oddSteps (C.word n) : ℕ) : ℤ) *
          (primitiveReturnGap C n : ℤ) := by
  simpa [AdjacentTransferChain.transfer] using
    primitiveKappa_eq_gap_balance C hN hNs hstart

end AdjacentTransferChain
end Synthesis
end Collatz2
