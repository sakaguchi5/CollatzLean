import CollatzLean.Collatz2.Global.CenterEscape
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Global: negative tail の moving center

隣接 center の運動を displacement-form separation で直接読む。
旧 `omegaAdjacent` は compatibility abbreviation にのみ残す。
chain-derived definition は実型の namespace `Collatz2.AdjacentTransferChain` に置き、
`C.returnGap`, `C.separationAdjacent` などを正規 dot notation で使えるようにする。
-/

namespace Collatz2
namespace AdjacentTransferChain

/-- Actual value gap of adjacent future-minimum block `n`. -/
def returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  C.endValue n - C.startValue n

/-- Actual adjacent return gap is positive. -/
theorem returnGap_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    0 < C.returnGap n := by
  unfold returnGap
  exact Nat.sub_pos_of_lt (C.startValue_lt_endValue n)

/-- Adjacent blocks share endpoint/start boundary. -/
@[simp] theorem endValue_eq_next_startValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.endValue n = C.startValue (n + 1) := by
  rfl

/-- Negative-block translation identity at the start: `B = G*x + A*delta`. -/
theorem translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    (C.transfer n).translate =
      (C.transfer n).centerGap * C.startValue n +
        (C.transfer n).twoCoeff * C.returnGap n := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  have hCA :
      (C.transfer n).oddCoeff ≤ (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hxy : C.startValue n ≤ C.endValue n :=
    (C.startValue_lt_endValue n).le
  have hA :
      (C.transfer n).centerGap + (C.transfer n).oddCoeff =
        (C.transfer n).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCA
  have hy :
      C.startValue n + C.returnGap n = C.endValue n := by
    unfold returnGap
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hxy)
  have hreal :
      (C.transfer n).twoCoeff * C.endValue n =
        (C.transfer n).oddCoeff * C.startValue n +
          (C.transfer n).translate := by
    simpa [AdjacentTransferChain.transfer, Word.Realizes,
      AffineTransfer.Realizes] using C.realizes n
  rw [← hA, ← hy] at hreal
  nlinarith

/-- Negative-block translation identity at endpoint: `B = G*y + C*delta`. -/
theorem translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    (C.transfer n).translate =
      (C.transfer n).centerGap * C.endValue n +
        (C.transfer n).oddCoeff * C.returnGap n := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  have hCA :
      (C.transfer n).oddCoeff ≤ (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hxy : C.startValue n ≤ C.endValue n :=
    (C.startValue_lt_endValue n).le
  have hA :
      (C.transfer n).centerGap + (C.transfer n).oddCoeff =
        (C.transfer n).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCA
  have hy :
      C.startValue n + C.returnGap n = C.endValue n := by
    unfold returnGap
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hxy)
  have hreal :
      (C.transfer n).twoCoeff * C.endValue n =
        (C.transfer n).oddCoeff * C.startValue n +
          (C.transfer n).translate := by
    simpa [AdjacentTransferChain.transfer, Word.Realizes,
      AffineTransfer.Realizes] using C.realizes n
  rw [← hA, ← hy] at hreal
  nlinarith

/-- Adjacent displacement-form separation. -/
def separationAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℤ :=
  (C.transfer n).separation (C.transfer (n + 1))

/-- Historical name retained as a compatibility abbreviation. -/
abbrev omegaAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℤ :=
  C.separationAdjacent n

/-- Adjacent center rise is exactly positive separation. -/
theorem centerRises_iff_separationAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    (C.transfer n).CenterRises (C.transfer (n + 1)) ↔
      0 < C.separationAdjacent n := by
  exact (C.transfer n).centerRises_iff_separation_pos (C.transfer (n + 1))

/-- Historical `omegaAdjacent` characterization. -/
theorem centerRises_iff_omegaAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    (C.transfer n).CenterRises (C.transfer (n + 1)) ↔
      0 < C.omegaAdjacent n :=
  C.centerRises_iff_separationAdjacent_pos n

/-- Consecutive negative blocks: separation is the center cross product. -/
theorem separationAdjacent_eq_center_cross
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1)) :
    C.separationAdjacent n =
      ((C.transfer n).centerGap : ℤ) *
          ((C.transfer (n + 1)).translate : ℤ) -
        ((C.transfer (n + 1)).centerGap : ℤ) *
          ((C.transfer n).translate : ℤ) := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  have hnegs : (C.transfer (n + 1)).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hNs
  unfold separationAdjacent
  rw [AffineTransfer.separation_eq,
    (C.transfer n).determinant_eq_neg_centerGap hneg,
    (C.transfer (n + 1)).determinant_eq_neg_centerGap hnegs]
  ring

/-- Historical theorem name. -/
theorem omegaAdjacent_eq_center_cross
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1)) :
    C.omegaAdjacent n =
      ((C.transfer n).centerGap : ℤ) *
          ((C.transfer (n + 1)).translate : ℤ) -
        ((C.transfer (n + 1)).centerGap : ℤ) *
          ((C.transfer n).translate : ℤ) :=
  C.separationAdjacent_eq_center_cross hN hNs

/--
Eliminating the shared boundary gives the exact adjacent return-gap balance.
-/
theorem separationAdjacent_eq_returnGap_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1)) :
    C.separationAdjacent n =
      ((C.transfer n).centerGap : ℤ) *
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
          (C.returnGap (n + 1) : ℤ) -
        ((C.transfer (n + 1)).centerGap : ℤ) *
          ((C.transfer n).oddCoeff : ℤ) *
          (C.returnGap n : ℤ) := by
  rw [C.separationAdjacent_eq_center_cross hN hNs]
  have hBn := C.translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap hN
  have hBns := C.translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap hNs
  have hBnZ :
      ((C.transfer n).translate : ℤ) =
        ((C.transfer n).centerGap : ℤ) * (C.endValue n : ℤ) +
          ((C.transfer n).oddCoeff : ℤ) * (C.returnGap n : ℤ) := by
    exact_mod_cast hBn
  have hBnsZ :
      ((C.transfer (n + 1)).translate : ℤ) =
        ((C.transfer (n + 1)).centerGap : ℤ) *
            (C.startValue (n + 1) : ℤ) +
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
            (C.returnGap (n + 1) : ℤ) := by
    exact_mod_cast hBns
  rw [hBnZ, hBnsZ, C.endValue_eq_next_startValue n]
  ring

/-- Historical theorem name. -/
theorem omegaAdjacent_eq_returnGap_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1)) :
    C.omegaAdjacent n =
      ((C.transfer n).centerGap : ℤ) *
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
          (C.returnGap (n + 1) : ℤ) -
        ((C.transfer (n + 1)).centerGap : ℤ) *
          ((C.transfer n).oddCoeff : ℤ) *
          (C.returnGap n : ℤ) :=
  C.separationAdjacent_eq_returnGap_balance hN hNs

/-- If all adjacent separations on a negative tail are nonpositive,
   every later center is below the tail start center. -/
theorem centerLe_tail_of_separationAdjacent_nonpos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {N : ℕ}
    (hNeg : ∀ n : ℕ, N ≤ n → C.NegativeAt n)
    (hsep : ∀ n : ℕ, N ≤ n → C.separationAdjacent n ≤ 0) :
    ∀ d : ℕ,
      (C.transfer (N + d)).CenterLe (C.transfer N) := by
  intro d
  induction d with
  | zero =>
      simpa using (C.transfer N).centerLe_refl
  | succ d ih =>
      have hstep :
          (C.transfer (N + d + 1)).CenterLe (C.transfer (N + d)) := by
        apply AffineTransfer.centerLe_reverse_of_separation_nonpos
        simpa [separationAdjacent, Nat.add_assoc] using hsep (N + d) (by omega)
      have hN0 : (C.transfer N).determinant < 0 := by
        simpa [AdjacentTransferChain.NegativeAt,
          AffineTransfer.NegativeDeterminant] using hNeg N (by omega)
      have hNd : (C.transfer (N + d)).determinant < 0 := by
        simpa [AdjacentTransferChain.NegativeAt,
          AffineTransfer.NegativeDeterminant] using hNeg (N + d) (by omega)
      have hNds : (C.transfer (N + d + 1)).determinant < 0 := by
        simpa [AdjacentTransferChain.NegativeAt,
          AffineTransfer.NegativeDeterminant] using hNeg (N + d + 1) (by omega)
      exact AffineTransfer.centerLe_trans_of_negative hNds hNd hN0 hstep ih

/-- Historical nonpositive-omega tail theorem. -/
theorem centerLe_tail_of_omegaAdjacent_nonpos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {N : ℕ}
    (hNeg : ∀ n : ℕ, N ≤ n → C.NegativeAt n)
    (hω : ∀ n : ℕ, N ≤ n → C.omegaAdjacent n ≤ 0) :
    ∀ d : ℕ,
      (C.transfer (N + d)).CenterLe (C.transfer N) :=
  C.centerLe_tail_of_separationAdjacent_nonpos hNeg hω

/-- A center beyond `U.translate` cannot lie below a negative center `U`. -/
theorem not_centerLe_of_centerBeyond_translate
    {T U : AffineTransfer}
    (hU : U.determinant < 0)
    (hBeyond : T.CenterBeyond U.translate) :
    ¬ T.CenterLe U := by
  intro hle
  have hBeyondOld := (T.centerBeyond_iff_gap_mul_lt_translate U.translate).mp hBeyond
  rcases hBeyondOld with ⟨hTgap, hBeyondIneq⟩
  have hUgap : (1 : ℤ) ≤ -U.determinant := by omega
  have hBnonneg : (0 : ℤ) ≤ (T.translate : ℤ) := by positivity
  have hgrow :
      (T.translate : ℤ) ≤
        (T.translate : ℤ) * (-U.determinant) := by
    have hm := mul_le_mul_of_nonneg_left hUgap hBnonneg
    simpa using hm
  unfold AffineTransfer.CenterLe at hle
  nlinarith

/-- Eventually-negative branch forces positive adjacent separation cofinally. -/
theorem separationAdjacent_pos_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => 0 < C.separationAdjacent n) := by
  classical
  by_contra hnot
  obtain ⟨K, hK⟩ := Cofinal.eventually_not_of_not hnot
  rcases hE with ⟨N, hN⟩
  let L := max N K
  have hNegL : ∀ n : ℕ, L ≤ n → C.NegativeAt n := by
    intro n hn
    exact hN n (le_trans (le_max_left _ _) hn)
  have hsepL : ∀ n : ℕ, L ≤ n → C.separationAdjacent n ≤ 0 := by
    intro n hn
    exact le_of_not_gt (hK n (le_trans (le_max_right _ _) hn))
  have hcofNeg : C.NegativeDeterminantCofinal :=
    C.negativeDeterminantCofinal_of_eventuallyNegative ⟨L, hNegL⟩
  obtain ⟨m, hmL, hmNeg, hmBeyond⟩ :=
    C.negativeCenters_cofinally_beyond hcofNeg (C.transfer L).translate L
  let d := m - L
  have hmEq : L + d = m := by
    dsimp [d]
    exact Nat.add_sub_of_le hmL
  have hboundD := C.centerLe_tail_of_separationAdjacent_nonpos hNegL hsepL d
  have hbound : (C.transfer m).CenterLe (C.transfer L) := by
    rw [← hmEq]
    exact hboundD
  have hLneg : (C.transfer L).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hNegL L (by omega)
  exact (not_centerLe_of_centerBeyond_translate hLneg hmBeyond) hbound

/-- Historical cofinal positive-omega theorem. -/
theorem omegaAdjacent_pos_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => 0 < C.omegaAdjacent n) :=
  C.separationAdjacent_pos_cofinal_of_eventuallyNegative hE

end AdjacentTransferChain
end Collatz2
