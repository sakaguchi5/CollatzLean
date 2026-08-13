import CollatzLean.Collatz2.Synthesis.GlobalCenterEscape
import CollatzLean.Collatz2.Matrix.CenterTransport
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Synthesis: moving centers on the eventually-negative tail

negative branch では common-center / changing-center を primitive branch にしない。
隣接 future-minimum blocks の center orientation を commutator `omega` で直接読む。

actual shared boundary を消去すると `omega` は二つの return gap の exact balance になる。
さらに eventually negative なら centers は infinity へ逃げるので、strict center rise
すなわち `omega > 0` が cofinally 強制される。
-/

namespace Collatz2
namespace Synthesis

open MatrixAnalysis

/-- contracting transfer の自然数 spectral gap `A-C`。 -/
def centerGap (T : AffineTransfer) : ℕ :=
  T.twoCoeff - T.oddCoeff

/-- negative determinant なら `centerGap > 0`。 -/
theorem centerGap_pos_of_negative
    {T : AffineTransfer}
    (hneg : T.determinant < 0) :
    0 < centerGap T := by
  unfold centerGap AffineTransfer.determinant at *
  omega

/-- negative determinant では signed determinant は `-centerGap`。 -/
theorem determinant_eq_neg_centerGap
    {T : AffineTransfer}
    (hneg : T.determinant < 0) :
    T.determinant = -(centerGap T : ℤ) := by
  have hle : T.oddCoeff ≤ T.twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  unfold centerGap AffineTransfer.determinant
  rw [Nat.cast_sub hle]
  ring

/-- 二つの finite centers の weak order を division-free cross product で表す。 -/
def CenterLe (T U : AffineTransfer) : Prop :=
  (T.translate : ℤ) * (-U.determinant) ≤
    (U.translate : ℤ) * (-T.determinant)

/-- 二つの finite centers の strict rise を division-free cross product で表す。 -/
def CenterRises (T U : AffineTransfer) : Prop :=
  (T.translate : ℤ) * (-U.determinant) <
    (U.translate : ℤ) * (-T.determinant)

/-- center rise は commutator scalar の正符号そのもの。 -/
theorem centerRises_iff_omega_pos
    (T U : AffineTransfer) :
    CenterRises T U ↔ 0 < MatrixAnalysis.omega T U := by
  unfold CenterRises MatrixAnalysis.omega
  constructor <;> intro h <;> nlinarith

/-- `omega ≤ 0` なら次 center は前 center 以下。 -/
theorem centerLe_reverse_of_omega_nonpos
    {T U : AffineTransfer}
    (hω : MatrixAnalysis.omega T U ≤ 0) :
    CenterLe U T := by
  unfold CenterLe MatrixAnalysis.omega at *
  nlinarith

/-- negative finite centers に対する cross-product order は推移的。 -/
theorem centerLe_trans_of_negative
    {T U V : AffineTransfer}
    (hT : T.determinant < 0)
    (hU : U.determinant < 0)
    (hV : V.determinant < 0)
    (hTU : CenterLe T U)
    (hUV : CenterLe U V) :
    CenterLe T V := by
  have gT : 0 < -T.determinant := by omega
  have gU : 0 < -U.determinant := by omega
  have gV : 0 < -V.determinant := by omega
  unfold CenterLe at hTU hUV ⊢
  have h1 := mul_le_mul_of_nonneg_right hTU (le_of_lt gV)
  have h2 := mul_le_mul_of_nonneg_right hUV (le_of_lt gT)
  have hchain :
      (T.translate : ℤ) * (-U.determinant) * (-V.determinant) ≤
        (V.translate : ℤ) * (-U.determinant) * (-T.determinant) := by
    calc
      (T.translate : ℤ) * (-U.determinant) * (-V.determinant)
          ≤ (U.translate : ℤ) * (-T.determinant) * (-V.determinant) := h1
      _ = (U.translate : ℤ) * (-V.determinant) * (-T.determinant) := by ring
      _ ≤ (V.translate : ℤ) * (-U.determinant) * (-T.determinant) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using h2
  have hcancel :
      (-U.determinant) *
          ((T.translate : ℤ) * (-V.determinant)) ≤
        (-U.determinant) *
          ((V.translate : ℤ) * (-T.determinant)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hchain
  exact (Int.mul_le_mul_left gU).mp hcancel

/-- center order の反射性。 -/
theorem centerLe_refl (T : AffineTransfer) : CenterLe T T := by
  unfold CenterLe
  exact le_rfl

namespace AdjacentTransferChain

/-- 第 `n` adjacent block の actual value gap。 -/
def returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℕ :=
  C.endValue n - C.startValue n

/-- actual adjacent return gap は正。 -/
theorem returnGap_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    0 < returnGap C n := by
  unfold returnGap
  exact Nat.sub_pos_of_lt (C.startValue_lt_endValue n)

/-- adjacent blocks は endpoint/start boundary を共有する。 -/
@[simp] theorem endValue_eq_next_startValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.endValue n = C.startValue (n + 1) := by
  rfl

/--
negative block の translation identity（start 版）。
`B = G*x + A*delta`。
-/
theorem translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    (C.transfer n).translate =
      centerGap (C.transfer n) * C.startValue n +
        (C.transfer n).twoCoeff * returnGap C n := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hN
  have hCA :
      (C.transfer n).oddCoeff ≤ (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hxy : C.startValue n ≤ C.endValue n :=
    (C.startValue_lt_endValue n).le
  have hA :
      centerGap (C.transfer n) + (C.transfer n).oddCoeff =
        (C.transfer n).twoCoeff := by
    unfold centerGap
    exact Nat.sub_add_cancel hCA
  have hy :
      C.startValue n + returnGap C n = C.endValue n := by
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

/--
negative block の translation identity（endpoint 版）。
`B = G*y + C*delta`。
-/
theorem translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    (C.transfer n).translate =
      centerGap (C.transfer n) * C.endValue n +
        (C.transfer n).oddCoeff * returnGap C n := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hN
  have hCA :
      (C.transfer n).oddCoeff ≤ (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hxy : C.startValue n ≤ C.endValue n :=
    (C.startValue_lt_endValue n).le
  have hA :
      centerGap (C.transfer n) + (C.transfer n).oddCoeff =
        (C.transfer n).twoCoeff := by
    unfold centerGap
    exact Nat.sub_add_cancel hCA
  have hy :
      C.startValue n + returnGap C n = C.endValue n := by
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

/-- adjacent block pair の commutator scalar。 -/
def omegaAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : ℤ :=
  MatrixAnalysis.omega (C.transfer n) (C.transfer (n + 1))

/-- adjacent center が上昇することと `omegaAdjacent > 0` は同値。 -/
theorem centerRises_iff_omegaAdjacent_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    CenterRises (C.transfer n) (C.transfer (n + 1)) ↔
      0 < omegaAdjacent C n := by
  exact centerRises_iff_omega_pos _ _

/-- consecutive negative blocks では omega は center cross product。 -/
theorem omegaAdjacent_eq_center_cross
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1)) :
    omegaAdjacent C n =
      (centerGap (C.transfer n) : ℤ) *
          ((C.transfer (n + 1)).translate : ℤ) -
        (centerGap (C.transfer (n + 1)) : ℤ) *
          ((C.transfer n).translate : ℤ) := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hN
  have hnegs : (C.transfer (n + 1)).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using hNs
  unfold omegaAdjacent MatrixAnalysis.omega
  rw [determinant_eq_neg_centerGap hneg,
    determinant_eq_neg_centerGap hnegs]
  ring

/--
shared future-minimum boundary を消去した exact adjacent-gap balance。

`omega_n = G_n A_(n+1) delta_(n+1) - G_(n+1) C_n delta_n`。
-/
theorem omegaAdjacent_eq_returnGap_balance
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1)) :
    omegaAdjacent C n =
      (centerGap (C.transfer n) : ℤ) *
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
          (returnGap C (n + 1) : ℤ) -
        (centerGap (C.transfer (n + 1)) : ℤ) *
          ((C.transfer n).oddCoeff : ℤ) *
          (returnGap C n : ℤ) := by
  rw [omegaAdjacent_eq_center_cross C hN hNs]
  have hBn := translate_eq_centerGap_mul_end_add_oddCoeff_mul_returnGap C hN
  have hBns := translate_eq_centerGap_mul_start_add_twoCoeff_mul_returnGap C hNs
  have hBnZ :
      ((C.transfer n).translate : ℤ) =
        (centerGap (C.transfer n) : ℤ) * (C.endValue n : ℤ) +
          ((C.transfer n).oddCoeff : ℤ) * (returnGap C n : ℤ) := by
    exact_mod_cast hBn
  have hBnsZ :
      ((C.transfer (n + 1)).translate : ℤ) =
        (centerGap (C.transfer (n + 1)) : ℤ) *
            (C.startValue (n + 1) : ℤ) +
          ((C.transfer (n + 1)).twoCoeff : ℤ) *
            (returnGap C (n + 1) : ℤ) := by
    exact_mod_cast hBns
  rw [hBnZ, hBnsZ, endValue_eq_next_startValue C n]
  ring

/--
negative tail で adjacent omega がすべて非正なら、各 later center は tail start 以下。
-/
theorem centerLe_tail_of_omegaAdjacent_nonpos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {N : ℕ}
    (hNeg : ∀ n : ℕ, N ≤ n → C.NegativeAt n)
    (hω : ∀ n : ℕ, N ≤ n → omegaAdjacent C n ≤ 0) :
    ∀ d : ℕ,
      CenterLe (C.transfer (N + d)) (C.transfer N) := by
  intro d
  induction d with
  | zero =>
      simpa using centerLe_refl (C.transfer N)
  | succ d ih =>
      have hstep :
          CenterLe (C.transfer (N + d + 1)) (C.transfer (N + d)) := by
        apply centerLe_reverse_of_omega_nonpos
        simpa [omegaAdjacent, Nat.add_assoc] using hω (N + d) (by omega)
      have hN0 : (C.transfer N).determinant < 0 := by
        simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant]
          using hNeg N (by omega)
      have hNd : (C.transfer (N + d)).determinant < 0 := by
        simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant]
          using hNeg (N + d) (by omega)
      have hNds : (C.transfer (N + d + 1)).determinant < 0 := by
        simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant] using
          hNeg (N + d + 1) (by omega)
      exact centerLe_trans_of_negative hNds hNd hN0 hstep ih

/--
center of `T` が `U.translate` より右にあるなら、negative `U` の center 以下ではありえない。
-/
theorem not_centerLe_of_centerBeyond_translate
    {T U : AffineTransfer}
    (hU : U.determinant < 0)
    (hBeyond : CenterBeyond T U.translate) :
    ¬ CenterLe T U := by
  intro hle
  rcases hBeyond with ⟨hTgap, hBeyond⟩
  have hUgap : (1 : ℤ) ≤ -U.determinant := by omega
  have hBnonneg : (0 : ℤ) ≤ (T.translate : ℤ) := by positivity
  have hgrow :
      (T.translate : ℤ) ≤
        (T.translate : ℤ) * (-U.determinant) := by
    have hm := mul_le_mul_of_nonneg_left hUgap hBnonneg
    simpa using hm
  unfold CenterLe at hle
  nlinarith

/--
eventually negative branch では strict adjacent center rise、すなわち `omega > 0` が cofinal。

common-center / changing-center を global top-level case split にする必要はない。
-/
theorem omegaAdjacent_pos_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => 0 < omegaAdjacent C n) := by
  classical
  by_contra hnot
  obtain ⟨K, hK⟩ := Cofinal.eventually_not_of_not hnot
  rcases hE with ⟨N, hN⟩
  let L := max N K
  have hNegL : ∀ n : ℕ, L ≤ n → C.NegativeAt n := by
    intro n hn
    exact hN n (le_trans (le_max_left _ _) hn)
  have hωL : ∀ n : ℕ, L ≤ n → omegaAdjacent C n ≤ 0 := by
    intro n hn
    exact le_of_not_gt (hK n (le_trans (le_max_right _ _) hn))
  have hcofNeg : C.NegativeDeterminantCofinal :=
    C.negativeDeterminantCofinal_of_eventuallyNegative ⟨L, hNegL⟩
  obtain ⟨m, hmL, hmNeg, hmBeyond⟩ :=
    negativeCenters_cofinally_beyond C hcofNeg (C.transfer L).translate L
  let d := m - L
  have hmEq : L + d = m := by
    dsimp [d]
    exact Nat.add_sub_of_le hmL
  have hboundD := centerLe_tail_of_omegaAdjacent_nonpos C hNegL hωL d
  have hbound : CenterLe (C.transfer m) (C.transfer L) := by
    rw [← hmEq]
    exact hboundD
  have hLneg : (C.transfer L).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt, AffineTransfer.NegativeDeterminant]
      using hNegL L (by omega)
  exact (not_centerLe_of_centerBeyond_translate hLneg hmBeyond) hbound

end AdjacentTransferChain
end Synthesis
end Collatz2
