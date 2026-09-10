import CollatzLean.Collatz3.Experimental2.MechanicalInverseCorridor

/-!
# Collatz3 Experimental2: inverse convergent corridor の endpoint glue

`MechanicalInverseCorridor` では正の residual threshold `k` に対して

`H(Q + k) = P + H(k)`

を証明した。

このファイルでは残っていた `k = 0` の seam を閉じる。
lower Farey orientation では current endpoint 自身が roof 上にあるため

`H(Q) = P`

となる。一方 upper orientation では current endpoint が exact に一段下

`β(P) = Q - 1`

にあるため

`H(Q) = P + 1`

となる。この一段差が upper corridor 固有の endpoint correction である。

さらに seam の inverse bit は

* lower: `1`
* upper: `0`

と exact に決まる。

新しい data definition は追加せず、既存 inverse / Farey corridor の derived theorem
だけで endpoint glue を与える。
-/

namespace Collatz3
namespace Experimental2

namespace IsLowerMechanicalRoof

/--
`1 ≤ σ` なら lower mechanical roof は index 自身以上にある。

`β(n) = floor(nσ)` と `n ≤ nσ` から従う。
-/
theorem index_le_roof_of_one_le_slope
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (n : ℕ) :
    n ≤ β n := by
  have hCell := M n
  have hnσ : (n : ℝ) ≤ (n : ℝ) * σ := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  have hLt : (n : ℝ) < ((β n + 1 : ℕ) : ℝ) :=
    lt_of_le_of_lt hnσ (by simpa using hCell.2)
  have hNat : n < β n + 1 := by
    exact_mod_cast hLt
  omega

/-- `1 ≤ σ` なら inverse height は threshold `1` を index `1` で初めて越える。 -/
@[simp] theorem inverse_one
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ) :
    M.inverse hσ 1 = 1 := by
  have hPos : 0 < M.inverse hσ 1 :=
    M.inverse_pos_of_pos hσ (by omega)
  have hUpper : M.inverse hσ 1 ≤ 1 := by
    simpa using M.inverse_succ_le_add_one hσ 0
  omega

/--
lower Farey corridor の `k = 0` endpoint。

current endpoint では `β(P) = Q` であり、`P` より前では lower corridor の
exact quotient formula によりまだ `Q` へ到達しない。従って `H(Q) = P`。
-/
theorem inverse_currentQ_eq_currentP_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn) :
    M.inverse hσ Q = P := by
  have hBetaP : β P = Q := by
    rw [M.eq_natFloor' P]
    exact natFloor_currentP_eq_Q_of_lowerFarey B hPLt
  have hPPos : 0 < P := B.1
  have hQPos : 0 < Q := by
    have hPQ : P ≤ Q := by
      rw [← hBetaP]
      exact M.index_le_roof_of_one_le_slope hσ P
    omega
  have hUpper : M.inverse hσ Q ≤ P := by
    apply M.inverse_le_of_reaches hσ
    rw [hBetaP]
  have hLower : P ≤ M.inverse hσ Q := by
    by_contra hNot
    have hInvLt : M.inverse hσ Q < P := by omega
    have hInvLtPn : M.inverse hσ Q < Pn :=
      lt_trans hInvLt hPLt
    have hBetaInv :
        β (M.inverse hσ Q) =
          (M.inverse hσ Q * Q) / P :=
      M.eq_current_div_of_lowerFarey B hInvLtPn
    have hSpec := M.inverse_spec hσ Q
    rw [hBetaInv] at hSpec
    have hMulLt :
        M.inverse hσ Q * Q < Q * P := by
      simpa [Nat.mul_comm] using
        Nat.mul_lt_mul_of_pos_right hInvLt hQPos
    have hDivLt :
        (M.inverse hσ Q * Q) / P < Q :=
      (Nat.div_lt_iff_lt_mul hPPos).2 hMulLt
    omega
  exact Nat.le_antisymm hUpper hLower

/--
upper Farey corridor の `k = 0` endpoint。

current endpoint は `β(P) = Q - 1` なので threshold `Q` にはまだ届かない。
一方 inverse は一 threshold ごとに高々一つしか増えないため、次の index で必ず届く。
従って `H(Q) = P + 1`。
-/
theorem inverse_currentQ_eq_currentP_add_one_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn) :
    M.inverse hσ Q = P + 1 := by
  have hBetaP : β P = Q - 1 := by
    rw [M.eq_natFloor' P]
    exact natFloor_currentP_eq_Q_sub_one_of_upperFarey B hPLt
  have hPPos : 0 < P := B.1
  have hQPos : 0 < Q := by
    have hPQPred : P ≤ Q - 1 := by
      rw [← hBetaP]
      exact M.index_le_roof_of_one_le_slope hσ P
    omega
  have hLower : P < M.inverse hσ Q := by
    by_contra hNot
    have hInvLe : M.inverse hσ Q ≤ P := by omega
    have hReach : Q ≤ β P :=
      (M.inverse_le_iff_of_monotone hσ hMono).1 hInvLe
    rw [hBetaP] at hReach
    omega
  have hPredReach : Q - 1 ≤ β P := by
    rw [hBetaP]
  have hInvPredLe : M.inverse hσ (Q - 1) ≤ P :=
    M.inverse_le_of_reaches hσ hPredReach
  have hStep := M.inverse_succ_le_add_one hσ (Q - 1)
  have hQSucc : Q - 1 + 1 = Q := by omega
  rw [hQSucc] at hStep
  have hUpper : M.inverse hσ Q ≤ P + 1 := by
    omega
  omega

/--
lower orientation では positive-domain translation を `k = 0` まで延長できる。

従って lower corridor は seam を含めて

`H(Q+k) = P+H(k)`

という一つの式で読める。
-/
theorem inverse_add_currentQ_eq_add_currentP_of_lowerFarey_including_zero
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hRange : P + M.inverse hσ k < Pn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  by_cases hk : k = 0
  · subst k
    have hPLt : P < Pn := by
      simpa using hRange
    simpa using M.inverse_currentQ_eq_currentP_of_lowerFarey hσ B hPLt
  · exact
      M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey
        hσ hMono B (Nat.pos_of_ne_zero hk) hRange

/--
upper orientation の endpoint correction を含む piecewise exact formula。

`k = 0` だけ `P+1`、`k > 0` では通常の `P+H(k)` translation になる。
-/
theorem inverse_add_currentQ_eq_of_upperFarey_piecewise
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hRange : P + M.inverse hσ k < Pn) :
    M.inverse hσ (Q + k) =
      if k = 0 then P + 1 else P + M.inverse hσ k := by
  by_cases hk : k = 0
  · subst k
    have hPLt : P < Pn := by
      simpa using hRange
    simp only [add_zero, ↓reduceIte]
    exact M.inverse_currentQ_eq_currentP_add_one_of_upperFarey
      hσ hMono B hPLt
  · rw [ite_eq_right hk]
    exact
      M.inverse_add_currentQ_eq_add_currentP_of_upperFarey
        hσ hMono B (Nat.pos_of_ne_zero hk) hRange

/--
lower corridor の seam bit は `1`。

lower orientation では `H(Q)=P` から `H(Q+1)=P+1` へ進む。
-/
theorem inverseStep_currentQ_eq_one_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hRange : P + 1 < Pn) :
    M.inverseStep hσ Q = 1 := by
  have hPLt : P < Pn := by omega
  have hEnd := M.inverse_currentQ_eq_currentP_of_lowerFarey hσ B hPLt
  have hOne : M.inverse hσ 1 = 1 := M.inverse_one hσ
  have hRangeOne : P + M.inverse hσ 1 < Pn := by
    simpa [hOne] using hRange
  have hNext :=
    M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey
      hσ hMono B (k := 1) (by omega) hRangeOne
  unfold inverseStep
  rw [hNext, hEnd, hOne]
  omega

/--
upper corridor の seam bit は `0`。

upper orientation では `H(Q)=P+1` であり、positive-domain translation から
`H(Q+1)=P+H(1)=P+1`。従って seam では plateau が一つ入る。
-/
theorem inverseStep_currentQ_eq_zero_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hRange : P + 1 < Pn) :
    M.inverseStep hσ Q = 0 := by
  have hPLt : P < Pn := by omega
  have hEnd :=
    M.inverse_currentQ_eq_currentP_add_one_of_upperFarey
      hσ hMono B hPLt
  have hOne : M.inverse hσ 1 = 1 := M.inverse_one hσ
  have hRangeOne : P + M.inverse hσ 1 < Pn := by
    simpa [hOne] using hRange
  have hNext :=
    M.inverse_add_currentQ_eq_add_currentP_of_upperFarey
      hσ hMono B (k := 1) (by omega) hRangeOne
  unfold inverseStep
  rw [hNext, hEnd, hOne]
  omega

end IsLowerMechanicalRoof

end Experimental2
end Collatz3
