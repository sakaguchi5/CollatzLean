import CollatzLean.Collatz2.Synthesis.MovingCenter
import CollatzLean.Collatz2.Orbit.FutureMinimumArithmetic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.GCD.Basic

/-!
# Collatz2 Synthesis: primitive center arithmetic

fixed-point vector `(B,G)` (`G=A-C>0`) の content を新しい branch data として置かない。
actual return gap `delta` と `G` の gcd から同じ content が導かれることを示し、
その gcd で割った primitive center を薄い quotient として読む。

future-minimum gap の4倍性を合わせると primitive center は

  `b / d = 3 + 4 * alpha / d`

の形になり、隣接 commutator は

  `omega = 4 * h * h' * kappa`

へ exact に factorize される。
-/

namespace Collatz2
namespace Synthesis

open MatrixAnalysis

namespace AdjacentTransferChain

/-- center vector `(B,G)` の content。 -/
def centerContent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  Nat.gcd (C.transfer n).translate (centerGap (C.transfer n))

/-- content を除いた primitive center numerator `b`。 -/
def primitiveCenterNumerator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (C.transfer n).translate / centerContent C n

/-- content を除いた primitive center denominator `d`。 -/
def primitiveCenterDenominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  centerGap (C.transfer n) / centerContent C n

/-- normalized center `b/d = 3 + 4*alpha/d` の `alpha`。 -/
def primitiveAlpha
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (primitiveCenterNumerator C n -
      3 * primitiveCenterDenominator C n) / 4

/-- adjacent primitive centers の signed unimodular separation。 -/
def primitiveKappa
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℤ :=
  (primitiveCenterDenominator C n : ℤ) *
      (primitiveAlpha C (n + 1) : ℤ) -
    (primitiveCenterDenominator C (n + 1) : ℤ) *
      (primitiveAlpha C n : ℤ)

/-- negative block では `A=twoCoeff` と `G=A-C` は coprime。 -/
theorem twoCoeff_coprime_centerGap_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime (C.transfer n).twoCoeff (centerGap (C.transfer n)) := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hN
  have hCA : (C.transfer n).oddCoeff ≤ (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hcopAC :
      Nat.Coprime (C.transfer n).twoCoeff (C.transfer n).oddCoeff := by
    change Nat.Coprime
      (2 ^ Word.twoSteps (C.word n))
      (3 ^ Word.oddSteps (C.word n))
    exact ((by decide : Nat.Coprime 2 3).pow_left _).pow_right _
  unfold centerGap
  exact (Nat.coprime_self_sub_right hCA).2 hcopAC

/--
fixed-point content は actual return gap と spectral gap の gcd そのもの。

`gcd(B,G) = gcd(delta,G)`。
-/
theorem centerContent_eq_returnGap_gcd
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    centerContent C n =
      Nat.gcd (returnGap C n) (centerGap (C.transfer n)) := by
  let T := C.transfer n
  let G := centerGap T
  let dlt := returnGap C n
  have hB := translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap C hN
  have hcopAG : Nat.Coprime T.twoCoeff G := by
    simpa [T, G] using twoCoeff_coprime_centerGap_of_negativeAt C hN
  have hfirst :
      Nat.gcd T.translate G = Nat.gcd (T.twoCoeff * dlt) G := by
    rw [hB]
    simp only [Nat.mul_comm, dvd_mul_left, Nat.gcd_add_left_left_of_dvd, G, T, dlt]
  have hsecond :
      Nat.gcd (T.twoCoeff * dlt) G = Nat.gcd dlt G := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · let g := Nat.gcd (T.twoCoeff * dlt) G
        have hgprod : g ∣ T.twoCoeff * dlt := Nat.gcd_dvd_left _ _
        have hgG : g ∣ G := Nat.gcd_dvd_right _ _
        have hcopgA : Nat.Coprime g T.twoCoeff :=
          (hcopAG.symm).of_dvd_left hgG
        exact hcopgA.dvd_of_dvd_mul_left hgprod
      · exact Nat.gcd_dvd_right _ _
    · apply Nat.dvd_gcd
      · have hd : Nat.gcd dlt G ∣ dlt := Nat.gcd_dvd_left _ _
        simpa [Nat.mul_comm] using dvd_mul_of_dvd_right hd T.twoCoeff
      · exact Nat.gcd_dvd_right _ _
  unfold centerContent
  simpa [T, G, dlt] using hfirst.trans hsecond

/-- negative block では center content は正。 -/
theorem centerContent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    0 < centerContent C n := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hN
  have hG : 0 < centerGap (C.transfer n) := centerGap_pos_of_negative hneg
  unfold centerContent
  exact Nat.gcd_pos_of_pos_right _ hG

/-- content は translation を割る。 -/
theorem centerContent_dvd_translate
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    centerContent C n ∣ (C.transfer n).translate := by
  unfold centerContent
  exact Nat.gcd_dvd_left _ _

/-- content は spectral gap を割る。 -/
theorem centerContent_dvd_centerGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    centerContent C n ∣ centerGap (C.transfer n) := by
  unfold centerContent
  exact Nat.gcd_dvd_right _ _

/-- `B = h*b`。 -/
theorem centerContent_mul_primitiveCenterNumerator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    centerContent C n * primitiveCenterNumerator C n =
      (C.transfer n).translate := by
  unfold primitiveCenterNumerator
  exact Nat.mul_div_cancel' (centerContent_dvd_translate C n)

/-- `G = h*d`。 -/
theorem centerContent_mul_primitiveCenterDenominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    centerContent C n * primitiveCenterDenominator C n =
      centerGap (C.transfer n) := by
  unfold primitiveCenterDenominator
  exact Nat.mul_div_cancel' (centerContent_dvd_centerGap C n)

/-- primitive numerator / denominator は coprime。 -/
theorem primitiveCenterNumerator_coprime_denominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime
      (primitiveCenterNumerator C n)
      (primitiveCenterDenominator C n) := by
  have hG : 0 < centerGap (C.transfer n) := by
    have hneg : (C.transfer n).determinant < 0 := by
      simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hN
    exact centerGap_pos_of_negative hneg
  have hgcd :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right
      (n := (C.transfer n).translate)
      (m := centerGap (C.transfer n))
      hG
  simpa [centerContent, primitiveCenterNumerator,
    primitiveCenterDenominator, Nat.Coprime] using hgcd

/-- content は actual return gap も割る。 -/
theorem centerContent_dvd_returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    centerContent C n ∣ returnGap C n := by
  rw [centerContent_eq_returnGap_gcd C hN]
  exact Nat.gcd_dvd_left _ _

/-- negative block では `4` と center content は coprime。 -/
theorem four_coprime_centerContent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime 4 (centerContent C n) := by
  have hcopAG := twoCoeff_coprime_centerGap_of_negativeAt C hN
  have hHpos : 0 < Word.twoSteps (C.word n) :=
    Word.twoSteps_pos_of_valid_nonempty (C.word_valid n) (C.word_nonempty n)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Word.twoSteps (C.word n) = k + 1 := by
    exact ⟨Word.twoSteps (C.word n) - 1, by omega⟩
  have h2A : 2 ∣ (C.transfer n).twoCoeff := by
    change 2 ∣ 2 ^ Word.twoSteps (C.word n)
    refine ⟨2 ^ k, ?_⟩
    rw [hk, pow_succ]
    ring
  have hcop2G : Nat.Coprime 2 (centerGap (C.transfer n)) :=
    hcopAG.of_dvd_left h2A
  have hcop2h : Nat.Coprime 2 (centerContent C n) :=
    hcop2G.of_dvd_right (centerContent_dvd_centerGap C n)
  have hpow := hcop2h.pow_left 2
  norm_num at hpow ⊢
  exact hpow

/--
start future minimum が `>1` なら primitive center は exact に
`b = 3*d + 4*alpha`、かつ `alpha,d` は coprime。
-/
theorem primitiveCenter_normal_form
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    primitiveCenterNumerator C n =
        3 * primitiveCenterDenominator C n +
          4 * primitiveAlpha C n ∧
      Nat.Coprime
        (primitiveAlpha C n)
        (primitiveCenterDenominator C n) := by
  let h := centerContent C n
  let b := primitiveCenterNumerator C n
  let d := primitiveCenterDenominator C n
  let s := returnGap C n / h
  have hhpos : 0 < h := by
    simpa [h] using centerContent_pos C hN
  have hhd : h * d = centerGap (C.transfer n) := by
    simpa [h, d] using centerContent_mul_primitiveCenterDenominator C n
  have hhb : h * b = (C.transfer n).translate := by
    simpa [h, b] using centerContent_mul_primitiveCenterNumerator C n
  have hhgap : h ∣ returnGap C n := centerContent_dvd_returnGap C hN
  have hhs : h * s = returnGap C n := by
    simpa [h, s] using Nat.mul_div_cancel' hhgap
  have hstartMin : 1 < O.value (C.minima.index n) := by
    simpa [AdjacentTransferChain.startValue,
      AdjacentTransferChain.startIndex] using hstart
  obtain ⟨q, _hqpos, hgap4⟩ := C.minima.valueGap_eq_four_mul hstartMin
  have hreturn4 : returnGap C n = 4 * q := by
    simpa [AdjacentTransferChain.returnGap,
      OddOrbit.FutureMinima.valueGap,
      AdjacentTransferChain.startValue,
      AdjacentTransferChain.endValue,
      AdjacentTransferChain.startIndex,
      AdjacentTransferChain.endIndex] using hgap4
  have hfourDivProd : 4 ∣ h * s := by
    rw [hhs, hreturn4]
    exact ⟨q, rfl⟩
  have hcop4h : Nat.Coprime 4 h := by
    simpa [h] using four_coprime_centerContent C hN
  have hfourDivS : 4 ∣ s :=
    hcop4h.dvd_of_dvd_mul_left hfourDivProd
  obtain ⟨t, ht⟩ := hfourDivS
  have hendgt : 1 < C.endValue n := by
    have hlt := C.startValue_lt_endValue n
    omega
  obtain ⟨m, hm⟩ :=
    (C.endFutureMinimum n).value_eq_four_mul_add_three hendgt
  have hmEnd :
    C.endValue n = 4 * m + 3 := by
    simpa [AdjacentTransferChain.endValue] using hm
  have hBend := translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap C hN
  have hcancel :
      h * b =
        h * (d * C.endValue n + (C.transfer n).oddCoeff * s) := by
    calc
      h * b = (C.transfer n).translate := hhb
      _ = centerGap (C.transfer n) * C.endValue n +
            (C.transfer n).oddCoeff * returnGap C n := hBend
      _ = (h * d) * C.endValue n +
            (C.transfer n).oddCoeff * (h * s) := by rw [hhd, hhs]
      _ = h * (d * C.endValue n + (C.transfer n).oddCoeff * s) := by ring
  have hbFormula :
      b = d * C.endValue n + (C.transfer n).oddCoeff * s :=
    Nat.mul_left_cancel hhpos hcancel
  have hnormalWitness :
      b = 3 * d +
        4 * (d * m + (C.transfer n).oddCoeff * t) := by
    rw [hbFormula, hmEnd, ht]
    ring
  have halpha :
      primitiveAlpha C n =
        d * m + (C.transfer n).oddCoeff * t := by
    change (b - 3 * d) / 4 = _
    rw [hnormalWitness]
    simp
  have hnormal :
      primitiveCenterNumerator C n =
        3 * primitiveCenterDenominator C n +
          4 * primitiveAlpha C n := by
    simpa [b, d, halpha] using hnormalWitness
  have hbd : Nat.Coprime b d := by
    simpa [b, d] using primitiveCenterNumerator_coprime_denominator C hN
  have had : Nat.Coprime (primitiveAlpha C n) d := by
    let g := Nat.gcd (primitiveAlpha C n) d
    have hga : g ∣ primitiveAlpha C n := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have hg3d : g ∣ 3 * d := by
      exact dvd_mul_of_dvd_right hgd 3
    have hg4a : g ∣ 4 * primitiveAlpha C n := by
      exact dvd_mul_of_dvd_right hga 4
    have hgb : g ∣ b := by
      have hadd : g ∣ 3 * d + 4 * primitiveAlpha C n := dvd_add hg3d hg4a
      simpa [b, d, hnormal] using hadd
    have hggcd : g ∣ Nat.gcd b d := Nat.dvd_gcd hgb hgd
    have hbdg : Nat.gcd b d = 1 := hbd
    rw [hbdg] at hggcd
    have hg1 : g = 1 := Nat.dvd_one.mp hggcd
    simpa [g] using hg1
  exact ⟨hnormal, by simpa [d] using had⟩

/--
consecutive negative blocks の commutator は primitive separation に exact factorize する。

`omega = 4*h*h'*kappa`。
-/
theorem omegaAdjacent_eq_four_mul_contents_mul_primitiveKappa
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    omegaAdjacent C n =
      4 * (centerContent C n : ℤ) *
        (centerContent C (n + 1) : ℤ) *
        primitiveKappa C n := by
  have hstartNext : 1 < C.startValue (n + 1) := by
    rw [← endValue_eq_next_startValue C n]
    exact lt_trans hstart (C.startValue_lt_endValue n)
  have hform := primitiveCenter_normal_form C hN hstart
  have hforms := primitiveCenter_normal_form C hNs hstartNext
  have hcross := omegaAdjacent_eq_center_cross C hN hNs
  have hGn :
      (centerGap (C.transfer n) : ℤ) =
        (centerContent C n : ℤ) *
          (primitiveCenterDenominator C n : ℤ) := by
    exact_mod_cast (centerContent_mul_primitiveCenterDenominator C n).symm
  have hGns :
      (centerGap (C.transfer (n + 1)) : ℤ) =
        (centerContent C (n + 1) : ℤ) *
          (primitiveCenterDenominator C (n + 1) : ℤ) := by
    exact_mod_cast (centerContent_mul_primitiveCenterDenominator C (n + 1)).symm
  have hBn :
      ((C.transfer n).translate : ℤ) =
        (centerContent C n : ℤ) *
          (primitiveCenterNumerator C n : ℤ) := by
    exact_mod_cast (centerContent_mul_primitiveCenterNumerator C n).symm
  have hBns :
      ((C.transfer (n + 1)).translate : ℤ) =
        (centerContent C (n + 1) : ℤ) *
          (primitiveCenterNumerator C (n + 1) : ℤ) := by
    exact_mod_cast (centerContent_mul_primitiveCenterNumerator C (n + 1)).symm
  have hformZ :
      (primitiveCenterNumerator C n : ℤ) =
        3 * (primitiveCenterDenominator C n : ℤ) +
          4 * (primitiveAlpha C n : ℤ) := by
    exact_mod_cast hform.1
  have hformsZ :
      (primitiveCenterNumerator C (n + 1) : ℤ) =
        3 * (primitiveCenterDenominator C (n + 1) : ℤ) +
          4 * (primitiveAlpha C (n + 1) : ℤ) := by
    exact_mod_cast hforms.1
  rw [hcross, hGn, hGns, hBn, hBns, hformZ, hformsZ]
  unfold primitiveKappa
  ring

/-- center-rise event では primitive `kappa` は正。 -/
theorem primitiveKappa_pos_of_omegaAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hω : 0 < omegaAdjacent C n) :
    0 < primitiveKappa C n := by
  have hfac :=
    omegaAdjacent_eq_four_mul_contents_mul_primitiveKappa C hN hNs hstart
  have hh : 0 < centerContent C n := centerContent_pos C hN
  have hhs : 0 < centerContent C (n + 1) := centerContent_pos C hNs
  have hcoef :
      (0 : ℤ) < 4 * (centerContent C n : ℤ) *
        (centerContent C (n + 1) : ℤ) := by
    positivity
  have hprod :
      0 <
        (4 * (centerContent C n : ℤ) *
          (centerContent C (n + 1) : ℤ)) * primitiveKappa C n := by
    rw [← hfac]
    exact hω
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · exfalso
    linarith

/-- integer `kappa` は center-rise event では少なくとも1。 -/
theorem one_le_primitiveKappa_of_omegaAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hω : 0 < omegaAdjacent C n) :
    (1 : ℤ) ≤ primitiveKappa C n := by
  have hk := primitiveKappa_pos_of_omegaAdjacent_pos C hN hNs hstart hω
  omega

end AdjacentTransferChain
end Synthesis
end Collatz2
