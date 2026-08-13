import CollatzLean.Collatz2.Global.PrimitiveCenter

/-!
# Collatz2 Global: primitive return-gap coordinates

negative future-minimum return gap を、同じ displacement root の center content で
primitive 化する。center-content の generic 定義は Geometry 側に置き、
このファイルでは chain 固有の return-gap / `alpha` / `kappa` arithmetic だけを扱う。
-/

namespace Collatz2
namespace AdjacentTransferChain

/-- Remove center content and the future-minimum factor `4` from return gap. -/
def primitiveReturnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (C.returnGap n / C.centerContent n) / 4

/-- Negative block with start `>1`: `returnGap = 4*h*s`. -/
theorem returnGap_eq_four_mul_content_mul_primitiveReturnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    C.returnGap n =
      4 * C.centerContent n * C.primitiveReturnGap n := by
  let h := C.centerContent n
  let t := C.returnGap n / h
  have hhgap : h ∣ C.returnGap n := C.centerContent_dvd_returnGap hN
  have hht : h * t = C.returnGap n := by
    simpa [h, t] using Nat.mul_div_cancel' hhgap
  have hstartMin : 1 < O.value (C.minima.index n) := by
    simpa [AdjacentTransferChain.startValue,
      AdjacentTransferChain.startIndex] using hstart
  obtain ⟨q, _hqpos, hgap4⟩ := C.minima.valueGap_eq_four_mul hstartMin
  have hreturn4 : C.returnGap n = 4 * q := by
    simpa [AdjacentTransferChain.returnGap,
      OddOrbit.FutureMinima.valueGap,
      AdjacentTransferChain.startValue,
      AdjacentTransferChain.endValue,
      AdjacentTransferChain.startIndex,
      AdjacentTransferChain.endIndex] using hgap4
  have hfourDivProd : 4 ∣ h * t := by
    rw [hht, hreturn4]
    exact ⟨q, rfl⟩
  have hcop4h : Nat.Coprime 4 h := by
    simpa [h] using C.four_coprime_centerContent hN
  have hfourDivT : 4 ∣ t :=
    hcop4h.dvd_of_dvd_mul_left hfourDivProd
  have hfourMul : 4 * (t / 4) = t :=
    Nat.mul_div_cancel' hfourDivT
  unfold primitiveReturnGap
  change C.returnGap n = 4 * h * (t / 4)
  calc
    C.returnGap n = h * t := hht.symm
    _ = h * (4 * (t / 4)) := by rw [hfourMul]
    _ = 4 * h * (t / 4) := by ring

/-- `(returnGap/h)` and primitive center denominator are coprime. -/
theorem returnGap_div_content_coprime_denominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime
      (C.returnGap n / C.centerContent n)
      (C.primitiveCenterDenominator n) := by
  have hG : 0 < (C.transfer n).centerGap := by
    have hneg : (C.transfer n).determinant < 0 := by
      simpa [AdjacentTransferChain.NegativeAt,
        AffineTransfer.NegativeDeterminant] using hN
    exact (C.transfer n).centerGap_pos_of_negative hneg
  have hgcd :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right
      (n := C.returnGap n)
      (m := (C.transfer n).centerGap)
      hG
  rw [← C.centerContent_eq_returnGap_gcd hN] at hgcd
  have hcontent :
      C.centerContent n =
        (C.transfer n).centerContent := by
    rfl
  change
    (C.returnGap n / C.centerContent n).gcd
      ((C.transfer n).centerGap /
        (C.transfer n).centerContent) = 1
  rw [← hcontent]
  exact hgcd

/-- Primitive return gap `s` and denominator `d` are coprime. -/
theorem primitiveReturnGap_coprime_denominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    Nat.Coprime
      (C.primitiveReturnGap n)
      (C.primitiveCenterDenominator n) := by
  have hcop := C.returnGap_div_content_coprime_denominator hN
  have hEq := C.returnGap_eq_four_mul_content_mul_primitiveReturnGap hN hstart
  have hhpos : 0 < C.centerContent n := C.centerContent_pos hN
  have hdiv :
      C.returnGap n / C.centerContent n = 4 * C.primitiveReturnGap n := by
    have hmul :
        C.returnGap n =
          C.centerContent n * (4 * C.primitiveReturnGap n) := by
      rw [hEq]
      ring
    exact Nat.div_eq_of_eq_mul_right hhpos hmul
  have hsdiv :
      C.primitiveReturnGap n ∣
        C.returnGap n / C.centerContent n := by
    rw [hdiv]
    exact dvd_mul_left _ _
  exact hcop.of_dvd_left hsdiv

/-- Negative word block natural center gap is odd. -/
theorem centerGap_odd_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Odd (C.transfer n).centerGap := by
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
  unfold AffineTransfer.centerGap
  rw [ha, hb]
  omega

/-- Center content is odd. -/
theorem centerContent_odd_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Odd (C.centerContent n) := by
  have hGodd := C.centerGap_odd_of_negativeAt hN
  have hfac := C.centerContent_mul_primitiveCenterDenominator n
  rw [← hfac] at hGodd
  exact Nat.Odd.of_mul_left hGodd

/-- Primitive center denominator is odd. -/
theorem primitiveCenterDenominator_odd_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Odd (C.primitiveCenterDenominator n) := by
  have hGodd := C.centerGap_odd_of_negativeAt hN
  have hfac := C.centerContent_mul_primitiveCenterDenominator n
  rw [← hfac] at hGodd
  exact Nat.Odd.of_mul_right hGodd

/-- Start coordinate form: `alpha = d*m + A*s`. -/
theorem primitiveAlpha_eq_start_coordinate
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    ∃ m : ℕ,
      C.startValue n = 4 * m + 3 ∧
      C.primitiveAlpha n =
        C.primitiveCenterDenominator n * m +
          (C.transfer n).twoCoeff * C.primitiveReturnGap n := by
  have hstartMin : 1 < O.value (C.startIndex n) := by
    simpa [AdjacentTransferChain.startValue] using hstart
  obtain ⟨m, hm⟩ :=
    (C.startFutureMinimum n).value_eq_four_mul_add_three hstartMin
  have hmStart : C.startValue n = 4 * m + 3 := by
    simpa [AdjacentTransferChain.startValue] using hm
  have hGap := C.returnGap_eq_four_mul_content_mul_primitiveReturnGap hN hstart
  have hB := C.translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap hN
  have hhb := C.centerContent_mul_primitiveCenterNumerator n
  have hhd := C.centerContent_mul_primitiveCenterDenominator n
  have hhpos : 0 < C.centerContent n := C.centerContent_pos hN
  let q :=
    C.primitiveCenterDenominator n * m +
      (C.transfer n).twoCoeff * C.primitiveReturnGap n
  have hbq :
      C.primitiveCenterNumerator n =
        3 * C.primitiveCenterDenominator n + 4 * q := by
    have hcancel :
      C.centerContent n * C.primitiveCenterNumerator n =
        C.centerContent n *
          (3 * C.primitiveCenterDenominator n + 4 * q) := by
      calc
        C.centerContent n * C.primitiveCenterNumerator n
            = (C.transfer n).translate := hhb
        _ = (C.transfer n).centerGap * C.startValue n +
              (C.transfer n).twoCoeff * C.returnGap n := hB
        _ =
            (C.centerContent n * C.primitiveCenterDenominator n) *
                (4 * m + 3) +
              (C.transfer n).twoCoeff *
                (4 * C.centerContent n * C.primitiveReturnGap n) := by
          rw [← hhd, hmStart, hGap]
        _ = C.centerContent n *
              (3 * C.primitiveCenterDenominator n + 4 * q) := by
          dsimp [q]
          ring
    exact Nat.mul_left_cancel hhpos hcancel
  have hnormal := (C.primitiveCenter_normal_form hN hstart).1
  have halpha : C.primitiveAlpha n = q := by omega
  exact ⟨m, by simpa [AdjacentTransferChain.startValue] using hm,
    by simpa [q] using halpha⟩

/-- Endpoint coordinate form: `alpha = d*m + C*s`. -/
theorem primitiveAlpha_eq_end_coordinate
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    ∃ m : ℕ,
      C.endValue n = 4 * m + 3 ∧
      C.primitiveAlpha n =
        C.primitiveCenterDenominator n * m +
          (C.transfer n).oddCoeff * C.primitiveReturnGap n := by
  have hend : 1 < C.endValue n :=
    lt_trans hstart (C.startValue_lt_endValue n)
  obtain ⟨m, hm⟩ :=
    (C.endFutureMinimum n).value_eq_four_mul_add_three hend
  have hmEnd : C.endValue n = 4 * m + 3 := by
    simpa [AdjacentTransferChain.endValue] using hm
  have hGap := C.returnGap_eq_four_mul_content_mul_primitiveReturnGap hN hstart
  have hB := C.translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap hN
  have hhb := C.centerContent_mul_primitiveCenterNumerator n
  have hhd := C.centerContent_mul_primitiveCenterDenominator n
  have hhpos : 0 < C.centerContent n := C.centerContent_pos hN
  let q :=
    C.primitiveCenterDenominator n * m +
      (C.transfer n).oddCoeff * C.primitiveReturnGap n
  have hbq :
      C.primitiveCenterNumerator n =
        3 * C.primitiveCenterDenominator n + 4 * q := by
    have hcancel :
        C.centerContent n * C.primitiveCenterNumerator n =
          C.centerContent n *
            (3 * C.primitiveCenterDenominator n + 4 * q) := by
      calc
        C.centerContent n * C.primitiveCenterNumerator n
            = (C.transfer n).translate := hhb
        _ = (C.transfer n).centerGap * C.endValue n +
              (C.transfer n).oddCoeff * C.returnGap n := hB
        _ =
            (C.centerContent n * C.primitiveCenterDenominator n) *
                (4 * m + 3) +
              (C.transfer n).oddCoeff *
                (4 * C.centerContent n * C.primitiveReturnGap n) := by
          rw [← hhd, hmEnd, hGap]
        _ = C.centerContent n *
              (3 * C.primitiveCenterDenominator n + 4 * q) := by
          dsimp [q]
          ring
    exact Nat.mul_left_cancel hhpos hcancel
  have hnormal := (C.primitiveCenter_normal_form hN hstart).1
  have halpha : C.primitiveAlpha n = q := by omega
  exact ⟨m, by simpa [AdjacentTransferChain.endValue] using hm,
    by simpa [q] using halpha⟩

/-- Exact primitive separation balance in return-gap coordinates. -/
theorem primitiveKappa_eq_gap_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    C.primitiveKappa n =
      (C.primitiveCenterDenominator n : ℤ) *
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
          (C.primitiveReturnGap (n + 1) : ℤ) -
        (C.primitiveCenterDenominator (n + 1) : ℤ) *
          ((C.transfer n).oddCoeff : ℤ) *
          (C.primitiveReturnGap n : ℤ) := by
  have hstartNext : 1 < C.startValue (n + 1) := by
    rw [← C.endValue_eq_next_startValue n]
    exact lt_trans hstart (C.startValue_lt_endValue n)
  have hGapN := C.returnGap_eq_four_mul_content_mul_primitiveReturnGap hN hstart
  have hGapNs := C.returnGap_eq_four_mul_content_mul_primitiveReturnGap hNs hstartNext
  have hGn := C.centerContent_mul_primitiveCenterDenominator n
  have hGns := C.centerContent_mul_primitiveCenterDenominator (n + 1)
  have hBal := C.separationAdjacent_eq_returnGap_balance hN hNs
  have hFac := C.separationAdjacent_eq_four_mul_contents_mul_primitiveKappa hN hNs hstart
  have hGapNZ :
      (C.returnGap n : ℤ) =
        4 * (C.centerContent n : ℤ) *
          (C.primitiveReturnGap n : ℤ) := by
    exact_mod_cast hGapN
  have hGapNsZ :
      (C.returnGap (n + 1) : ℤ) =
        4 * (C.centerContent (n + 1) : ℤ) *
          (C.primitiveReturnGap (n + 1) : ℤ) := by
    exact_mod_cast hGapNs
  have hGnZ :
      ((C.transfer n).centerGap : ℤ) =
        (C.centerContent n : ℤ) *
          (C.primitiveCenterDenominator n : ℤ) := by
    exact_mod_cast hGn.symm
  have hGnsZ :
      ((C.transfer (n + 1)).centerGap : ℤ) =
        (C.centerContent (n + 1) : ℤ) *
          (C.primitiveCenterDenominator (n + 1) : ℤ) := by
    exact_mod_cast hGns.symm
  let R : ℤ :=
    (C.primitiveCenterDenominator n : ℤ) *
        ((C.transfer (n + 1)).twoCoeff : ℤ) *
        (C.primitiveReturnGap (n + 1) : ℤ) -
      (C.primitiveCenterDenominator (n + 1) : ℤ) *
        ((C.transfer n).oddCoeff : ℤ) *
        (C.primitiveReturnGap n : ℤ)
  have hBal' :
      C.separationAdjacent n =
        4 * (C.centerContent n : ℤ) *
          (C.centerContent (n + 1) : ℤ) * R := by
    rw [hBal, hGnZ, hGnsZ, hGapNZ, hGapNsZ]
    dsimp [R]
    ring
  have hcoef :
      (4 : ℤ) * (C.centerContent n : ℤ) *
        (C.centerContent (n + 1) : ℤ) ≠ 0 := by
    have hn := C.centerContent_pos hN
    have hns := C.centerContent_pos hNs
    positivity
  have heq :
      (4 : ℤ) * (C.centerContent n : ℤ) *
          (C.centerContent (n + 1) : ℤ) * C.primitiveKappa n =
        (4 : ℤ) * (C.centerContent n : ℤ) *
          (C.centerContent (n + 1) : ℤ) * R := by
    rw [← hFac, ← hBal']
  have hcancel := mul_left_cancel₀ hcoef heq
  simpa [R] using hcancel

/-- Expanded word-coefficient form. -/
theorem primitiveKappa_eq_twoPow_threePow_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    C.primitiveKappa n =
      (C.primitiveCenterDenominator n : ℤ) *
          ((2 ^ Word.twoSteps (C.word (n + 1)) : ℕ) : ℤ) *
          (C.primitiveReturnGap (n + 1) : ℤ) -
        (C.primitiveCenterDenominator (n + 1) : ℤ) *
          ((3 ^ Word.oddSteps (C.word n) : ℕ) : ℤ) *
          (C.primitiveReturnGap n : ℤ) := by
  simpa [AdjacentTransferChain.transfer] using
    C.primitiveKappa_eq_gap_balance hN hNs hstart

end AdjacentTransferChain
end Collatz2
