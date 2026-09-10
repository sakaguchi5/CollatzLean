import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridor
import CollatzLean.Collatz3.Experimental2.MechanicalInverse

/-!
# Collatz3 Experimental2: convergent corridor の離散逆

`MechanicalConvergentCorridor` は lower mechanical roof

`β(n) = floor(n * σ)`

について、consecutive Farey / convergent bracket `(P,Q),(Pn,Qn)` の内側で

`β(P + x) = Q + β(x)`

という exact corridor を与える。

`MechanicalInverse` は同じ roof の離散逆

`H(k) = min {m | k ≤ β(m)}`

を与える。

このファイルでは二つを合成し、corridor が inverse 側でも

`H(Q + k) = P + H(k)`

という exact block translation を与えることを示す。
さらに inverse の一歩差分も `Q` shift で exact に反復する。

この層は generic であり、`2`, `3`, `beattyIndex`, `RecordFerrers` を導入しない。
新しい data definition も追加せず、既存の roof / inverse / Farey bracket だけを使う。
-/

namespace Collatz3
namespace Experimental2

namespace IsLowerMechanicalRoof

/--
roof が単調なら、canonical inverse は threshold について exact な順序逆を持つ。

`H(k) ≤ m ↔ k ≤ β(m)`。

右向きは inverse の最小性、左向きは inverse 自身での到達と roof の単調性だけを使う。
-/
theorem inverse_le_iff_of_monotone
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {k m : ℕ} :
    M.inverse hσ k ≤ m ↔ k ≤ β m := by
  constructor
  · intro hInv
    exact le_trans (M.inverse_spec hσ k) (hMono hInv)
  · intro hReach
    exact M.inverse_le_of_reaches hσ hReach

/-- 正の threshold の canonical inverse は正。 -/
theorem inverse_pos_of_pos
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {k : ℕ}
    (hk : 0 < k) :
    0 < M.inverse hσ k := by
  by_contra hNot
  have hZero : M.inverse hσ k = 0 :=
    Nat.eq_zero_of_not_pos hNot
  have hSpec := M.inverse_spec hσ k
  have hBetaZero : β 0 = 0 := by
    have h := M.eq_natFloor' 0
    simpa using h
  rw [hZero, hBetaZero] at hSpec
  omega

/--
lower Farey corridor を inverse 側へ exact に転置する。

roof 側の

`β(P+x) = Q+β(x)`

に対応して、corridor 内では

`H(Q+k) = P+H(k)`

となる。
-/
theorem inverse_add_currentQ_eq_add_currentP_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + M.inverse hσ k < Pn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  let H := M.inverse hσ k
  have hHPos : 0 < H := by
    dsimp [H]
    exact M.inverse_pos_of_pos hσ hk
  have hRangeH : P + H < Pn := by
    simpa [H] using hRange
  have hPLt : P < Pn := by omega
  have hPeriodicH : β (P + H) = Q + β H :=
    M.add_currentP_eq_add_Q_of_lowerFarey B hRangeH
  have hUpper : M.inverse hσ (Q + k) ≤ P + H := by
    apply M.inverse_le_of_reaches hσ
    rw [hPeriodicH]
    have hSpec := M.inverse_spec hσ k
    have hSpecH : k ≤ β H := by
      simpa [H] using hSpec
    omega
  have hLower : P + H ≤ M.inverse hσ (Q + k) := by
    by_contra hNot
    have hInvLt : M.inverse hσ (Q + k) < P + H := by omega
    have hInvSpec := M.inverse_spec hσ (Q + k)
    by_cases hAtMostP : M.inverse hσ (Q + k) ≤ P
    · have hMonoP :
          β (M.inverse hσ (Q + k)) ≤ β P :=
        hMono hAtMostP
      have hBetaP : β P = Q := by
        rw [M.eq_natFloor' P]
        exact natFloor_currentP_eq_Q_of_lowerFarey B hPLt
      rw [hBetaP] at hMonoP
      omega
    · have hPastP : P < M.inverse hσ (Q + k) :=
        Nat.lt_of_not_ge hAtMostP
      let x := M.inverse hσ (Q + k) - P
      have hxPos : 0 < x := by
        dsimp [x]
        omega
      have hPx : P + x = M.inverse hσ (Q + k) := by
        dsimp [x]
        omega
      have hxLtH : x < H := by
        dsimp [x]
        omega
      have hRangeX : P + x < Pn := by
        rw [hPx]
        exact lt_trans hInvLt hRangeH
      have hPeriodicX : β (P + x) = Q + β x :=
        M.add_currentP_eq_add_Q_of_lowerFarey B hRangeX
      have hMinX : β x < k :=
        M.inverse_min hσ (k := k) hxLtH
      have hBetaInv :
          β (M.inverse hσ (Q + k)) = Q + β x := by
        rw [← hPx]
        exact hPeriodicX
      rw [hBetaInv] at hInvSpec
      omega
  exact Nat.le_antisymm hUpper hLower

/--
upper Farey corridor も、positive inverse domain では同じ exact translation を持つ。

`x=0` では roof 側に upper orientation 固有の `-1` correction があるため、
最小性の証明では current endpoint `P` を別に処理する。
-/
theorem inverse_add_currentQ_eq_add_currentP_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + M.inverse hσ k < Pn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  let H := M.inverse hσ k
  have hHPos : 0 < H := by
    dsimp [H]
    exact M.inverse_pos_of_pos hσ hk
  have hRangeH : P + H < Pn := by
    simpa [H] using hRange
  have hPLt : P < Pn := by omega
  have hPeriodicH : β (P + H) = Q + β H :=
    M.add_currentP_eq_add_Q_of_upperFarey B hHPos hRangeH
  have hUpper : M.inverse hσ (Q + k) ≤ P + H := by
    apply M.inverse_le_of_reaches hσ
    rw [hPeriodicH]
    have hSpec := M.inverse_spec hσ k
    have hSpecH : k ≤ β H := by
      simpa [H] using hSpec
    omega
  have hLower : P + H ≤ M.inverse hσ (Q + k) := by
    by_contra hNot
    have hInvLt : M.inverse hσ (Q + k) < P + H := by omega
    have hInvSpec := M.inverse_spec hσ (Q + k)
    by_cases hAtMostP : M.inverse hσ (Q + k) ≤ P
    · have hMonoP :
          β (M.inverse hσ (Q + k)) ≤ β P :=
        hMono hAtMostP
      have hBetaP : β P = Q - 1 := by
        rw [M.eq_natFloor' P]
        exact natFloor_currentP_eq_Q_sub_one_of_upperFarey B hPLt
      rw [hBetaP] at hMonoP
      omega
    · have hPastP : P < M.inverse hσ (Q + k) :=
        Nat.lt_of_not_ge hAtMostP
      let x := M.inverse hσ (Q + k) - P
      have hxPos : 0 < x := by
        dsimp [x]
        omega
      have hPx : P + x = M.inverse hσ (Q + k) := by
        dsimp [x]
        omega
      have hxLtH : x < H := by
        dsimp [x]
        omega
      have hRangeX : P + x < Pn := by
        rw [hPx]
        exact lt_trans hInvLt hRangeH
      have hPeriodicX : β (P + x) = Q + β x :=
        M.add_currentP_eq_add_Q_of_upperFarey B hxPos hRangeX
      have hMinX : β x < k :=
        M.inverse_min hσ (k := k) hxLtH
      have hBetaInv :
          β (M.inverse hσ (Q + k)) = Q + β x := by
        rw [← hPx]
        exact hPeriodicX
      rw [hBetaInv] at hInvSpec
      omega
  exact Nat.le_antisymm hUpper hLower

/--
lower corridor では inverse の一歩差分が `Q` shift で exact に反復する。

これは inverse Sturmian word の finite exact block repetition。
-/
theorem inverseStep_add_currentQ_eq_inverseStep_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + M.inverse hσ (k + 1) < Pn) :
    M.inverseStep hσ (Q + k) = M.inverseStep hσ k := by
  have hInvMono := M.inverse_le_succ hσ k
  have hRange0 : P + M.inverse hσ k < Pn := by omega
  have hShift0 :=
    M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey
      hσ hMono B hk hRange0
  have hShift1 :=
    M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey
      hσ hMono B (k := k + 1) (by omega) hRange
  unfold inverseStep
  rw [show Q + k + 1 = Q + (k + 1) by omega]
  rw [hShift1, hShift0]
  omega

/-- upper corridor でも positive domain では inverse bit が `Q` shift で exact に反復する。 -/
theorem inverseStep_add_currentQ_eq_inverseStep_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + M.inverse hσ (k + 1) < Pn) :
    M.inverseStep hσ (Q + k) = M.inverseStep hσ k := by
  have hInvMono := M.inverse_le_succ hσ k
  have hRange0 : P + M.inverse hσ k < Pn := by omega
  have hShift0 :=
    M.inverse_add_currentQ_eq_add_currentP_of_upperFarey
      hσ hMono B hk hRange0
  have hShift1 :=
    M.inverse_add_currentQ_eq_add_currentP_of_upperFarey
      hσ hMono B (k := k + 1) (by omega) hRange
  unfold inverseStep
  rw [show Q + k + 1 = Q + (k + 1) by omega]
  rw [hShift1, hShift0]
  omega

end IsLowerMechanicalRoof

end Experimental2
end Collatz3
