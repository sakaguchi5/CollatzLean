import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridorSharp

/-!
# Collatz3 Experimental2: sharp lower endpoint の最終整理

`MechanicalConvergentCorridorSharp` では positive residual に対する lower inverse corridor

`H(Q+k) = P + H(k)`

を自然 range `0 < k < Qn` まで強化した。

ここでは lower endpoint 自身

`H(Q) = P`

から、従来残っていた補助仮定 `P < Pn` を除去する。

核心は、`m < P` で既に `β(m) ≥ Q` だと仮定すると、
`β(m)/m` が current lower fraction `Q/P` と next upper fraction `Qn/Pn`
の間に入り、Farey denominator barrier に反することである。

従って lower orientation では current/next の分母大小に依存せず、
current point `(P,Q)` が threshold `Q` の exact first contact になる。
-/

namespace Collatz3
namespace Experimental2

namespace IsLowerMechanicalRoof

/--
lower Farey endpoint は `P < Pn` を仮定せず exact に `β(P)=Q`。

sharp roof corridor の `x=0` を使うだけでよい。
-/
theorem roof_currentP_eq_currentQ_of_lowerFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn) :
    β P = Q := by
  have hBetaZero : β 0 = 0 := by
    rw [M.eq_natFloor' 0]
    simp
  have h := M.add_currentP_eq_add_Q_of_lowerFarey_sharp
    B (x := 0) B.2.1
  simpa [hBetaZero] using h

/--
lower Farey endpoint より前では threshold `Q` に届かない。

`m=0` は直接処理する。`0<m<P` で `Q ≤ β(m)` を仮定すると、
`β(m)/m` は current fraction `Q/P` より真に上、かつ mechanical roof の定義から
slope `σ` 以下である。next upper fraction は `σ` より上なので、この分数は
current/next の strict interval に入る。しかし denominator `m<P<P+Pn` は
Farey denominator barrier と矛盾する。
-/
theorem roof_lt_currentQ_before_currentP_of_lowerFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {P Q Pn Qn m : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hm : m < P) :
    β m < Q := by
  have hBetaP : β P = Q :=
    M.roof_currentP_eq_currentQ_of_lowerFarey_sharp B
  have hPPos : 0 < P := B.1
  have hQPos : 0 < Q := by
    have hPQ : P ≤ Q := by
      rw [← hBetaP]
      exact M.index_le_roof_of_one_le_slope hσ P
    omega
  by_cases hm0 : m = 0
  · subst m
    rw [M.eq_natFloor' 0]
    simp [hQPos]
  · have hmPos : 0 < m := Nat.pos_of_ne_zero hm0
    by_contra hNot
    have hQle : Q ≤ β m := by omega
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmPos
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPPos
    have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast B.2.1
    have hLeftNat : Q * m < β m * P := by
      have hQPmul : Q * m < Q * P :=
        Nat.mul_lt_mul_of_pos_left hm hQPos
      have hQPBeta : Q * P ≤ β m * P :=
        Nat.mul_le_mul_right P hQle
      exact lt_of_lt_of_le hQPmul hQPBeta
    have hRoofR : (β m : ℝ) ≤ (m : ℝ) * σ := (M m).1
    have hNextMul : σ * (Pn : ℝ) < (Qn : ℝ) :=
      (lt_div_iff₀ hPnR).1 B.2.2.2.1
    have hRightR :
        (β m : ℝ) * (Pn : ℝ) < (Qn : ℝ) * (m : ℝ) := by
      calc
        (β m : ℝ) * (Pn : ℝ)
            ≤ ((m : ℝ) * σ) * (Pn : ℝ) :=
              mul_le_mul_of_nonneg_right hRoofR (le_of_lt hPnR)
        _ = (m : ℝ) * (σ * (Pn : ℝ)) := by ring
        _ < (m : ℝ) * (Qn : ℝ) :=
              mul_lt_mul_of_pos_left hNextMul hmR
        _ = (Qn : ℝ) * (m : ℝ) := by ring
    have hRightNat : β m * Pn < Qn * m := by
      exact_mod_cast hRightR
    have hBarrier : P + Pn ≤ m :=
      denominator_add_le_of_between_lower_determinant
        hLeftNat hRightNat B.2.2.2.2
    omega

/--
lower Farey endpoint の inverse height は、current/next の分母大小に依存せず exact に `P`。

従来の `inverse_currentQ_eq_currentP_of_lowerFarey` にあった `P<Pn` は不要である。
-/
theorem inverse_currentQ_eq_currentP_of_lowerFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn) :
    M.inverse hσ Q = P := by
  have hBetaP : β P = Q :=
    M.roof_currentP_eq_currentQ_of_lowerFarey_sharp B
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
    have hSpec := M.inverse_spec hσ Q
    have hBefore :=
      M.roof_lt_currentQ_before_currentP_of_lowerFarey_sharp
        hσ B hInvLt
    omega
  exact Nat.le_antisymm hUpper hLower

/--
lower sharp inverse corridor は residual `0` を含めても `P<Pn` を必要としない。
-/
theorem inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp_including_zero_no_lt
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hk : k < Qn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  by_cases hk0 : k = 0
  · subst k
    simp only [add_zero, M.inverse_zero hσ]
    exact M.inverse_currentQ_eq_currentP_of_lowerFarey_sharp hσ B
  · exact M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
      hσ hMono B (Nat.pos_of_ne_zero hk0) hk

/--
lower seam bit も `P<Pn` なしで exact に `1`。
自然 range として必要なのは `1<Qn` だけである。
-/
theorem inverseStep_currentQ_eq_one_of_lowerFarey_sharp_no_lt
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hOneLt : 1 < Qn) :
    M.inverseStep hσ Q = 1 := by
  have hEnd := M.inverse_currentQ_eq_currentP_of_lowerFarey_sharp hσ B
  have hOne : M.inverse hσ 1 = 1 := M.inverse_one hσ
  have hNext := M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    hσ hMono B (k := 1) (by omega) hOneLt
  unfold inverseStep
  rw [hNext, hEnd, hOne]
  omega

end IsLowerMechanicalRoof

end Experimental2
end Collatz3
