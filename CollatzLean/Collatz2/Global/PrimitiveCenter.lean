import CollatzLean.Collatz2.Global.MovingCenter
import CollatzLean.Collatz2.Geometry.PrimitiveForm
import CollatzLean.Collatz2.Orbit.FutureMinimumArithmetic
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Global: primitive displacement-root arithmetic

content / primitive pair 自体は generic `AffineTransfer` に属する。
ここでは future-minimum 固有の `alpha`, `kappa` と global consequence だけを追加する。
すべて実型 namespace `Collatz2.AdjacentTransferChain` に置く。
-/

namespace Collatz2
namespace AdjacentTransferChain

/-- Content of block `n`'s negative displacement form. -/
def centerContent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (C.transfer n).centerContent

/-- Primitive center numerator. -/
def primitiveCenterNumerator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (C.transfer n).primitiveCenterNumerator

/-- Primitive center denominator. -/
def primitiveCenterDenominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (C.transfer n).primitiveCenterDenominator

/-- Normalized future-minimum coordinate in `b = 3*d + 4*alpha`. -/
def primitiveAlpha
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  (C.primitiveCenterNumerator n -
      3 * C.primitiveCenterDenominator n) / 4

/-- Signed separation of adjacent primitive center coordinates. -/
def primitiveKappa
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℤ :=
  (C.primitiveCenterDenominator n : ℤ) *
      (C.primitiveAlpha (n + 1) : ℤ) -
    (C.primitiveCenterDenominator (n + 1) : ℤ) *
      (C.primitiveAlpha n : ℤ)

/-- Negative word block: `A` and `G=A-C` are coprime. -/
theorem twoCoeff_coprime_centerGap_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime (C.transfer n).twoCoeff (C.transfer n).centerGap := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  have hCA : (C.transfer n).oddCoeff ≤ (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hcopAC :
      Nat.Coprime (C.transfer n).twoCoeff (C.transfer n).oddCoeff := by
    change Nat.Coprime
      (2 ^ Word.twoSteps (C.word n))
      (3 ^ Word.oddSteps (C.word n))
    exact ((by decide : Nat.Coprime 2 3).pow_left _).pow_right _
  unfold AffineTransfer.centerGap
  exact (Nat.coprime_self_sub_right hCA).2 hcopAC

/-- `gcd(B,G) = gcd(returnGap,G)`. -/
theorem centerContent_eq_returnGap_gcd
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    C.centerContent n =
      Nat.gcd (C.returnGap n) (C.transfer n).centerGap := by
  let T := C.transfer n
  let G := T.centerGap
  let dlt := C.returnGap n
  have hB := C.translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap hN
  have hcopAG : Nat.Coprime T.twoCoeff G := by
    simpa [T, G] using C.twoCoeff_coprime_centerGap_of_negativeAt hN
  have hfirst :
      Nat.gcd T.translate G = Nat.gcd (T.twoCoeff * dlt) G := by
    rw [hB]
    simp only [Nat.mul_comm, dvd_mul_left,
      Nat.gcd_add_left_left_of_dvd, G, T, dlt]
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
  unfold centerContent AffineTransfer.centerContent
  simpa [T, G, dlt] using hfirst.trans hsecond

/-- Negative block has positive center content. -/
theorem centerContent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    0 < C.centerContent n := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  exact (C.transfer n).centerContent_pos_of_negative hneg

/-- Content divides translation. -/
theorem centerContent_dvd_translate
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.centerContent n ∣ (C.transfer n).translate := by
  exact (C.transfer n).centerContent_dvd_translate

/-- Content divides center gap. -/
theorem centerContent_dvd_centerGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.centerContent n ∣ (C.transfer n).centerGap := by
  exact (C.transfer n).centerContent_dvd_centerGap

/-- `B = h*b`. -/
theorem centerContent_mul_primitiveCenterNumerator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.centerContent n * C.primitiveCenterNumerator n =
      (C.transfer n).translate := by
  exact (C.transfer n).centerContent_mul_primitiveCenterNumerator

/-- `G = h*d`. -/
theorem centerContent_mul_primitiveCenterDenominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.centerContent n * C.primitiveCenterDenominator n =
      (C.transfer n).centerGap := by
  exact (C.transfer n).centerContent_mul_primitiveCenterDenominator

/-- Primitive numerator/denominator are coprime. -/
theorem primitiveCenterNumerator_coprime_denominator
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime
      (C.primitiveCenterNumerator n)
      (C.primitiveCenterDenominator n) := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  exact (C.transfer n).primitiveCenterNumerator_coprime_denominator_of_negative hneg

/-- Center content also divides the actual return gap. -/
theorem centerContent_dvd_returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    C.centerContent n ∣ C.returnGap n := by
  rw [C.centerContent_eq_returnGap_gcd hN]
  exact Nat.gcd_dvd_left _ _

/-- On a negative word block, `4` is coprime to center content. -/
theorem four_coprime_centerContent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Nat.Coprime 4 (C.centerContent n) := by
  have hcopAG := C.twoCoeff_coprime_centerGap_of_negativeAt hN
  have hHpos : 0 < Word.twoSteps (C.word n) :=
    Word.twoSteps_pos_of_valid_nonempty (C.word_valid n) (C.word_nonempty n)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Word.twoSteps (C.word n) = k + 1 := by
    exact ⟨Word.twoSteps (C.word n) - 1, by omega⟩
  have h2A : 2 ∣ (C.transfer n).twoCoeff := by
    change 2 ∣ 2 ^ Word.twoSteps (C.word n)
    refine ⟨2 ^ k, ?_⟩
    rw [hk, pow_succ]
    ring
  have hcop2G : Nat.Coprime 2 (C.transfer n).centerGap :=
    hcopAG.of_dvd_left h2A
  have hcop2h : Nat.Coprime 2 (C.centerContent n) :=
    hcop2G.of_dvd_right (C.centerContent_dvd_centerGap n)
  have hpow := hcop2h.pow_left 2
  norm_num at hpow ⊢
  exact hpow

/--
For start future minimum `>1`, primitive center has exact normal form
`b = 3*d + 4*alpha`, with `gcd(alpha,d)=1`.
-/
theorem primitiveCenter_normal_form
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hstart : 1 < C.startValue n) :
    C.primitiveCenterNumerator n =
        3 * C.primitiveCenterDenominator n +
          4 * C.primitiveAlpha n ∧
      Nat.Coprime
        (C.primitiveAlpha n)
        (C.primitiveCenterDenominator n) := by
  let h := C.centerContent n
  let b := C.primitiveCenterNumerator n
  let d := C.primitiveCenterDenominator n
  let s := C.returnGap n / h
  have hhpos : 0 < h := by
    simpa [h] using C.centerContent_pos hN
  have hhd : h * d = (C.transfer n).centerGap := by
    simpa [h, d] using C.centerContent_mul_primitiveCenterDenominator n
  have hhb : h * b = (C.transfer n).translate := by
    simpa [h, b] using C.centerContent_mul_primitiveCenterNumerator n
  have hhgap : h ∣ C.returnGap n := C.centerContent_dvd_returnGap hN
  have hhs : h * s = C.returnGap n := by
    simpa [h, s] using Nat.mul_div_cancel' hhgap
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
  have hfourDivProd : 4 ∣ h * s := by
    rw [hhs, hreturn4]
    exact ⟨q, rfl⟩
  have hcop4h : Nat.Coprime 4 h := by
    simpa [h] using C.four_coprime_centerContent hN
  have hfourDivS : 4 ∣ s :=
    hcop4h.dvd_of_dvd_mul_left hfourDivProd
  obtain ⟨t, ht⟩ := hfourDivS
  have hendgt : 1 < C.endValue n := by
    have hlt := C.startValue_lt_endValue n
    omega
  obtain ⟨m, hm⟩ :=
    (C.endFutureMinimum n).value_eq_four_mul_add_three hendgt
  have hmEnd : C.endValue n = 4 * m + 3 := by
    simpa [AdjacentTransferChain.endValue] using hm
  have hBend := C.translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap hN
  have hcancel :
      h * b =
        h * (d * C.endValue n + (C.transfer n).oddCoeff * s) := by
    calc
      h * b = (C.transfer n).translate := hhb
      _ = (C.transfer n).centerGap * C.endValue n +
            (C.transfer n).oddCoeff * C.returnGap n := hBend
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
      C.primitiveAlpha n =
        d * m + (C.transfer n).oddCoeff * t := by
    change (b - 3 * d) / 4 = _
    rw [hnormalWitness]
    simp
  have hnormal :
      C.primitiveCenterNumerator n =
        3 * C.primitiveCenterDenominator n +
          4 * C.primitiveAlpha n := by
    simpa [b, d, halpha] using hnormalWitness
  have hbd : Nat.Coprime b d := by
    simpa [b, d] using C.primitiveCenterNumerator_coprime_denominator hN
  have had : Nat.Coprime (C.primitiveAlpha n) d := by
    let g := Nat.gcd (C.primitiveAlpha n) d
    have hga : g ∣ C.primitiveAlpha n := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have hg3d : g ∣ 3 * d := dvd_mul_of_dvd_right hgd 3
    have hg4a : g ∣ 4 * C.primitiveAlpha n :=
      dvd_mul_of_dvd_right hga 4
    have hgb : g ∣ b := by
      have hadd : g ∣ 3 * d + 4 * C.primitiveAlpha n := dvd_add hg3d hg4a
      simpa [b, d, hnormal] using hadd
    have hggcd : g ∣ Nat.gcd b d := Nat.dvd_gcd hgb hgd
    have hbdg : Nat.gcd b d = 1 := hbd
    rw [hbdg] at hggcd
    have hg1 : g = 1 := Nat.dvd_one.mp hggcd
    simpa [g] using hg1
  exact ⟨hnormal, by simpa [d] using had⟩

/-- Adjacent separation factors as `4*h*h'*kappa`. -/
theorem separationAdjacent_eq_four_mul_contents_mul_primitiveKappa
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    C.separationAdjacent n =
      4 * (C.centerContent n : ℤ) *
        (C.centerContent (n + 1) : ℤ) *
        C.primitiveKappa n := by
  have hstartNext : 1 < C.startValue (n + 1) := by
    rw [← C.endValue_eq_next_startValue n]
    exact lt_trans hstart (C.startValue_lt_endValue n)
  have hform := C.primitiveCenter_normal_form hN hstart
  have hforms := C.primitiveCenter_normal_form hNs hstartNext
  have hcross := C.separationAdjacent_eq_center_cross hN hNs
  have hGn :
      ((C.transfer n).centerGap : ℤ) =
        (C.centerContent n : ℤ) *
          (C.primitiveCenterDenominator n : ℤ) := by
    exact_mod_cast (C.centerContent_mul_primitiveCenterDenominator n).symm
  have hGns :
      ((C.transfer (n + 1)).centerGap : ℤ) =
        (C.centerContent (n + 1) : ℤ) *
          (C.primitiveCenterDenominator (n + 1) : ℤ) := by
    exact_mod_cast (C.centerContent_mul_primitiveCenterDenominator (n + 1)).symm
  have hBn :
      ((C.transfer n).translate : ℤ) =
        (C.centerContent n : ℤ) *
          (C.primitiveCenterNumerator n : ℤ) := by
    exact_mod_cast (C.centerContent_mul_primitiveCenterNumerator n).symm
  have hBns :
      ((C.transfer (n + 1)).translate : ℤ) =
        (C.centerContent (n + 1) : ℤ) *
          (C.primitiveCenterNumerator (n + 1) : ℤ) := by
    exact_mod_cast (C.centerContent_mul_primitiveCenterNumerator (n + 1)).symm
  have hformZ :
      (C.primitiveCenterNumerator n : ℤ) =
        3 * (C.primitiveCenterDenominator n : ℤ) +
          4 * (C.primitiveAlpha n : ℤ) := by
    exact_mod_cast hform.1
  have hformsZ :
      (C.primitiveCenterNumerator (n + 1) : ℤ) =
        3 * (C.primitiveCenterDenominator (n + 1) : ℤ) +
          4 * (C.primitiveAlpha (n + 1) : ℤ) := by
    exact_mod_cast hforms.1
  rw [hcross, hGn, hGns, hBn, hBns, hformZ, hformsZ]
  unfold primitiveKappa
  ring

/-- Historical omega factorization theorem. -/
theorem omegaAdjacent_eq_four_mul_contents_mul_primitiveKappa
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n) :
    C.omegaAdjacent n =
      4 * (C.centerContent n : ℤ) *
        (C.centerContent (n + 1) : ℤ) *
        C.primitiveKappa n :=
  C.separationAdjacent_eq_four_mul_contents_mul_primitiveKappa hN hNs hstart

/-- Positive adjacent separation gives positive primitive kappa. -/
theorem primitiveKappa_pos_of_separationAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hsep : 0 < C.separationAdjacent n) :
    0 < C.primitiveKappa n := by
  have hfac := C.separationAdjacent_eq_four_mul_contents_mul_primitiveKappa hN hNs hstart
  have hh : 0 < C.centerContent n := C.centerContent_pos hN
  have hhs : 0 < C.centerContent (n + 1) := C.centerContent_pos hNs
  have hcoef :
      (0 : ℤ) < 4 * (C.centerContent n : ℤ) *
        (C.centerContent (n + 1) : ℤ) := by
    positivity
  have hprod :
      0 <
        (4 * (C.centerContent n : ℤ) *
          (C.centerContent (n + 1) : ℤ)) * C.primitiveKappa n := by
    rw [← hfac]
    exact hsep
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · exfalso
    linarith

/-- Historical omega-positive theorem. -/
theorem primitiveKappa_pos_of_omegaAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hω : 0 < C.omegaAdjacent n) :
    0 < C.primitiveKappa n :=
  C.primitiveKappa_pos_of_separationAdjacent_pos hN hNs hstart hω

/-- Positive separation gives integer `kappa >= 1`. -/
theorem one_le_primitiveKappa_of_separationAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hsep : 0 < C.separationAdjacent n) :
    (1 : ℤ) ≤ C.primitiveKappa n := by
  have hk := C.primitiveKappa_pos_of_separationAdjacent_pos hN hNs hstart hsep
  omega

/-- Historical omega-positive integer lower bound. -/
theorem one_le_primitiveKappa_of_omegaAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hω : 0 < C.omegaAdjacent n) :
    (1 : ℤ) ≤ C.primitiveKappa n :=
  C.one_le_primitiveKappa_of_separationAdjacent_pos hN hNs hstart hω

/-- Eventually-negative branch forces `primitiveKappa >= 1` cofinally. -/
theorem primitiveKappa_one_le_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => (1 : ℤ) ≤ C.primitiveKappa n) := by
  have hSep : Cofinal (fun n => 0 < C.separationAdjacent n) :=
    C.separationAdjacent_pos_cofinal_of_eventuallyNegative hE
  rcases hE with ⟨Nneg, hNeg⟩
  obtain ⟨Nval, hVal⟩ := C.minima.values_eventually_large 1
  intro M
  let L := max M (max Nneg Nval)
  obtain ⟨n, hnL, hSepN⟩ := hSep L
  have hML : M ≤ L := le_max_left _ _
  have hTailL : max Nneg Nval ≤ L := le_max_right _ _
  have hNegL : Nneg ≤ L := le_trans (le_max_left _ _) hTailL
  have hValL : Nval ≤ L := le_trans (le_max_right _ _) hTailL
  have hnM : M ≤ n := le_trans hML hnL
  have hnNeg : Nneg ≤ n := le_trans hNegL hnL
  have hnVal : Nval ≤ n := le_trans hValL hnL
  have hN : C.NegativeAt n := hNeg n hnNeg
  have hNs : C.NegativeAt (n + 1) := hNeg (n + 1) (by omega)
  have hstart : 1 < C.startValue n := by
    have h := hVal n hnVal
    simpa [AdjacentTransferChain.startValue,
      AdjacentTransferChain.startIndex] using h
  exact ⟨n, hnM,
    C.one_le_primitiveKappa_of_separationAdjacent_pos hN hNs hstart hSepN⟩

/-- Eventually-negative branch forces positive primitive kappa cofinally. -/
theorem primitiveKappa_pos_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => 0 < C.primitiveKappa n) := by
  have hK := C.primitiveKappa_one_le_cofinal_of_eventuallyNegative hE
  intro M
  obtain ⟨n, hnM, hnK⟩ := hK M
  exact ⟨n, hnM, lt_of_lt_of_le (by omega) hnK⟩

end AdjacentTransferChain
end Collatz2
