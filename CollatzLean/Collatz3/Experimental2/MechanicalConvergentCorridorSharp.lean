import CollatzLean.Collatz3.Experimental2.MechanicalInverseCorridorEndpoint
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: Farey corridor の自然な全幅への強化

既存の `MechanicalConvergentCorridor` / `MechanicalInverseCorridor` では、
current block を足した後も next denominator の手前に残るという十分条件

`P + x < Pn`, `P + H(k) < Pn`

を使っていた。

しかし consecutive Farey pair の determinant `±1` からは、より自然な

* roof 側: `x < Pn`
* inverse 側: `k < Qn`

という全幅 corridor が得られる。

roof 側の核心は Farey 隣接分数の denominator barrier である。
current fraction と next fraction の間に別の有理数 `A / D` が入れば、
`D` は少なくとも `P + Pn` でなければならない。
従って `D = P + x`, `x < Pn` では中間分数は存在できない。

inverse 側では、positive residual の全域で

`H(Q+k) = P + H(k)`

が成立する。`k = 0` だけは既存 endpoint theorem の通り、
lower で補正 `0`、upper で補正 `1` を持つ。
-/

namespace Collatz3
namespace Experimental2

/--
lower determinant orientation の Farey denominator barrier。

`Q/P < A/D < Qn/Pn` なら `P + Pn ≤ D`。
分数の既約性は不要で、strict cross-multiplication と determinant `1` だけでよい。
-/
theorem denominator_add_le_of_between_lower_determinant
    {P Q Pn Qn A D : ℕ}
    (hLeft : Q * D < A * P)
    (hRight : A * Pn < Qn * D)
    (hDet : Pn * Q + 1 = P * Qn) :
    P + Pn ≤ D := by
  have hLeftOne : Q * D + 1 ≤ A * P := by omega
  have hRightOne : A * Pn + 1 ≤ Qn * D := by omega
  have hL := Nat.mul_le_mul_left Pn hLeftOne
  have hR := Nat.mul_le_mul_left P hRightOne
  have hSum := Nat.add_le_add hL hR
  have hDetD : P * Qn * D = Pn * Q * D + D := by
    calc
      P * Qn * D = (P * Qn) * D := by ring
      _ = (Pn * Q + 1) * D := by rw [← hDet]
      _ = Pn * Q * D + D := by ring
  ring_nf at hSum hDetD
  omega

/--
upper determinant orientation の Farey denominator barrier。

`Qn/Pn < A/D < Q/P` なら同じく `P + Pn ≤ D`。
-/
theorem denominator_add_le_of_between_upper_determinant
    {P Q Pn Qn A D : ℕ}
    (hLeft : Qn * D < A * Pn)
    (hRight : A * P < Q * D)
    (hDet : P * Qn + 1 = Pn * Q) :
    P + Pn ≤ D := by
  have hLeftOne : Qn * D + 1 ≤ A * Pn := by omega
  have hRightOne : A * P + 1 ≤ Q * D := by omega
  have hL := Nat.mul_le_mul_left P hLeftOne
  have hR := Nat.mul_le_mul_left Pn hRightOne
  have hSum := Nat.add_le_add hL hR
  have hDetD : Pn * Q * D = P * Qn * D + D := by
    calc
      Pn * Q * D = (Pn * Q) * D := by ring
      _ = (P * Qn + 1) * D := by rw [← hDet]
      _ = P * Qn * D + D := by ring
  ring_nf at hSum hDetD
  omega

namespace IsLowerMechanicalRoof

/-- lower mechanical roof は加法に関して超加法的。 -/
theorem add_le_add_roof
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (a b : ℕ) :
    β a + β b ≤ β (a + b) := by
  have ha := M a
  have hb := M b
  have hab := M (a + b)
  have hR :
      (((β a + β b : ℕ) : ℝ)) <
        (((β (a + b) + 1 : ℕ) : ℝ)) := by
    calc
      (((β a + β b : ℕ) : ℝ))
          = (β a : ℝ) + (β b : ℝ) := by norm_num
      _ ≤ (a : ℝ) * σ + (b : ℝ) * σ := add_le_add ha.1 hb.1
      _ = ((a + b : ℕ) : ℝ) * σ := by push_cast; ring
      _ < (((β (a + b) + 1 : ℕ) : ℝ)) := by simpa using hab.2
  have hN : β a + β b < β (a + b) + 1 := by exact_mod_cast hR
  omega

/--
lower Farey corridor の roof translation は residual `x < Pn` の全域で成立する。

失敗を仮定すると `(Q + β(x) + 1)/(P+x)` が current / next の間へ入り、
Farey denominator barrier と `x < Pn` が矛盾する。
-/
theorem add_currentP_eq_add_Q_of_lowerFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn x : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hx : x < Pn) :
    β (P + x) = Q + β x := by
  rcases B with ⟨hP, hPn, hCurrent, hNext, hDet⟩
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast hPn
  have hDR : (0 : ℝ) < ((P + x : ℕ) : ℝ) := by positivity
  have hCurrentMul : (Q : ℝ) < σ * (P : ℝ) :=
    (div_lt_iff₀ hPR).1 hCurrent
  have hNextMul : σ * (Pn : ℝ) < (Qn : ℝ) :=
    (lt_div_iff₀ hPnR).1 hNext
  have hBaseR :
      (((Q + β x : ℕ) : ℝ)) < ((P + x : ℕ) : ℝ) * σ := by
    calc
      (((Q + β x : ℕ) : ℝ)) = (Q : ℝ) + (β x : ℝ) := by norm_num
      _ < σ * (P : ℝ) + (x : ℝ) * σ :=
        add_lt_add_of_lt_of_le hCurrentMul (M x).1
      _ = ((P + x : ℕ) : ℝ) * σ := by push_cast; ring
  have hBaseNat : Q + β x < β (P + x) + 1 := by
    exact_mod_cast (lt_trans hBaseR (M (P + x)).2)
  have hBase : Q + β x ≤ β (P + x) := by omega
  apply Nat.le_antisymm
  · by_contra hNot
    have hStrict : Q + β x < β (P + x) := by omega
    let A : ℕ := Q + β x + 1
    let D : ℕ := P + x
    have hA_le : A ≤ β (P + x) := by
      dsimp [A]
      omega
    have hAReal : (A : ℝ) ≤ ((P + x : ℕ) : ℝ) * σ := by
      exact le_trans (by exact_mod_cast hA_le) (M (P + x)).1
    have hRightR :
        (A : ℝ) * (Pn : ℝ) < (Qn : ℝ) * (D : ℝ) := by
      calc
        (A : ℝ) * (Pn : ℝ)
            ≤ (((P + x : ℕ) : ℝ) * σ) * (Pn : ℝ) :=
              mul_le_mul_of_nonneg_right hAReal (le_of_lt hPnR)
        _ = ((P + x : ℕ) : ℝ) * (σ * (Pn : ℝ)) := by ring
        _ < ((P + x : ℕ) : ℝ) * (Qn : ℝ) :=
              mul_lt_mul_of_pos_left hNextMul hDR
        _ = (Qn : ℝ) * (D : ℝ) := by dsimp [D]; ring
    have hRightNat : A * Pn < Qn * D := by exact_mod_cast hRightR
    have hBetaZero : β 0 = 0 := by
      rw [M.eq_natFloor' 0]
      simp
    have hLeftNat : Q * D < A * P := by
      by_cases hx0 : x = 0
      · subst x
        dsimp [A, D]
        rw [hBetaZero]
        calc
          Q * P < Q * P + P := by omega
          _ = (Q + 0 + 1) * P := by ring
      · have hxPos : 0 < x := Nat.pos_of_ne_zero hx0
        have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxPos
        have hXQ :
            (x : ℝ) * (Q : ℝ) <
              (P : ℝ) * (((β x + 1 : ℕ) : ℝ)) := by
          calc
            (x : ℝ) * (Q : ℝ)
                < (x : ℝ) * (σ * (P : ℝ)) :=
                  mul_lt_mul_of_pos_left hCurrentMul hxR
            _ = (P : ℝ) * ((x : ℝ) * σ) := by ring
            _ < (P : ℝ) * (((β x + 1 : ℕ) : ℝ)) :=
                  mul_lt_mul_of_pos_left (by simpa using (M x).2) hPR
        have hLeftR :
            (Q : ℝ) * (D : ℝ) < (A : ℝ) * (P : ℝ) := by
          dsimp [A, D]
          push_cast
          have hXQ' :
              (x : ℝ) * (Q : ℝ) <
                (P : ℝ) * ((β x : ℝ) + 1) := by
            simpa using hXQ
          calc
            (Q : ℝ) * ((P : ℝ) + (x : ℝ))
                = (Q : ℝ) * (P : ℝ) + (x : ℝ) * (Q : ℝ) := by
                  ring
            _ < (Q : ℝ) * (P : ℝ) +
                  (P : ℝ) * ((β x : ℝ) + 1) := by
                  linarith
            _ = ((Q : ℝ) + (β x : ℝ) + 1) * (P : ℝ) := by ring
        exact_mod_cast hLeftR
    have hBarrier : P + Pn ≤ D :=
      denominator_add_le_of_between_lower_determinant
        hLeftNat hRightNat hDet
    dsimp [D] at hBarrier
    omega
  · exact hBase

/--
upper Farey corridor でも positive residual `0 < x < Pn` の全域で
`β(P+x) = Q + β(x)` が成立する。

`x=0` だけは upper endpoint 固有の `Q-1` correction を持つため除外する。
-/
theorem add_currentP_eq_add_Q_of_upperFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn x : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hxPos : 0 < x)
    (hx : x < Pn) :
    β (P + x) = Q + β x := by
  rcases B with ⟨hP, hPn, hNext, hCurrent, hDet⟩
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast hPn
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxPos
  have hDR : (0 : ℝ) < ((P + x : ℕ) : ℝ) := by positivity
  have hNextMul : (Qn : ℝ) < σ * (Pn : ℝ) :=
    (div_lt_iff₀ hPnR).1 hNext
  have hCurrentMul : σ * (P : ℝ) < (Q : ℝ) :=
    (lt_div_iff₀ hPR).1 hCurrent
  have hCurrentMul' : (P : ℝ) * σ < (Q : ℝ) := by
    simpa [mul_comm] using hCurrentMul
  have hUpperR :
      ((β (P + x) : ℕ) : ℝ) <
        (((Q + β x + 1 : ℕ) : ℝ)) := by
    have hMxUpper :
        (x : ℝ) * σ < (((β x + 1 : ℕ) : ℝ)) := by
      simpa using (M x).2
    calc
      ((β (P + x) : ℕ) : ℝ)
          ≤ ((P + x : ℕ) : ℝ) * σ := (M (P + x)).1
      _ = (P : ℝ) * σ + (x : ℝ) * σ := by
            push_cast
            ring
      _ < (Q : ℝ) + (((β x + 1 : ℕ) : ℝ)) := by
            exact add_lt_add hCurrentMul' hMxUpper
      _ = (((Q + β x + 1 : ℕ) : ℝ)) := by
            push_cast
            ring
  have hUpperNat : β (P + x) < Q + β x + 1 := by exact_mod_cast hUpperR
  have hUpper : β (P + x) ≤ Q + β x := by omega
  apply Nat.le_antisymm hUpper
  by_contra hNot
  have hStrict : β (P + x) < Q + β x := by omega
  let A : ℕ := Q + β x
  let D : ℕ := P + x
  have hSucc_le : β (P + x) + 1 ≤ A := by
    dsimp [A]
    omega
  have hSigma_lt_A : ((P + x : ℕ) : ℝ) * σ < (A : ℝ) := by
    exact lt_of_lt_of_le (M (P + x)).2 (by exact_mod_cast hSucc_le)
  have hLeftR :
      (Qn : ℝ) * (D : ℝ) < (A : ℝ) * (Pn : ℝ) := by
    calc
      (Qn : ℝ) * (D : ℝ)
          < (σ * (Pn : ℝ)) * ((P + x : ℕ) : ℝ) := by
              dsimp [D]
              exact mul_lt_mul_of_pos_right hNextMul hDR
      _ = (((P + x : ℕ) : ℝ) * σ) * (Pn : ℝ) := by ring
      _ < (A : ℝ) * (Pn : ℝ) :=
            mul_lt_mul_of_pos_right hSigma_lt_A hPnR
  have hLeftNat : Qn * D < A * Pn := by exact_mod_cast hLeftR
  have hBetaX_lt :
      (β x : ℝ) * (P : ℝ) < (x : ℝ) * (Q : ℝ) := by
    calc
      (β x : ℝ) * (P : ℝ)
          ≤ ((x : ℝ) * σ) * (P : ℝ) :=
            mul_le_mul_of_nonneg_right (M x).1 (le_of_lt hPR)
      _ = (x : ℝ) * (σ * (P : ℝ)) := by ring
      _ < (x : ℝ) * (Q : ℝ) :=
            mul_lt_mul_of_pos_left hCurrentMul hxR
  have hRightR :
      (A : ℝ) * (P : ℝ) < (Q : ℝ) * (D : ℝ) := by
    dsimp [A, D]
    push_cast
    calc
      ((Q : ℝ) + (β x : ℝ)) * (P : ℝ)
          = (Q : ℝ) * (P : ℝ) + (β x : ℝ) * (P : ℝ) := by
              ring
      _ < (Q : ℝ) * (P : ℝ) + (x : ℝ) * (Q : ℝ) := by
            linarith [hBetaX_lt]
      _ = (Q : ℝ) * ((P : ℝ) + (x : ℝ)) := by
            ring
  have hRightNat : A * P < Q * D := by exact_mod_cast hRightR
  have hBarrier : P + Pn ≤ D :=
    denominator_add_le_of_between_upper_determinant
      hLeftNat hRightNat hDet
  dsimp [D] at hBarrier
  omega

/-- lower bracket の next denominator では少なくとも `Qn-1` まで roof が到達する。 -/
theorem nextQ_pred_le_roof_nextP_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn) :
    Qn - 1 ≤ β Pn := by
  rcases B with ⟨hP, hPn, hCurrent, hNext, hDet⟩
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast hPn
  have hQnPos : 0 < Qn := by
    by_contra hNot
    have hQn0 : Qn = 0 := Nat.eq_zero_of_not_pos hNot
    subst Qn
    norm_num at hNext
    linarith
  have hCurrentMul : (Q : ℝ) < σ * (P : ℝ) :=
    (div_lt_iff₀ hPR).1 hCurrent
  have hScaled :
      (Pn : ℝ) * (Q : ℝ) <
        (Pn : ℝ) * σ * (P : ℝ) := by
    calc
      (Pn : ℝ) * (Q : ℝ)
          < (Pn : ℝ) * (σ * (P : ℝ)) :=
              mul_lt_mul_of_pos_left hCurrentMul hPnR
      _ = (Pn : ℝ) * σ * (P : ℝ) := by ring
  have hDetR :
      (Pn : ℝ) * (Q : ℝ) + 1 = (P : ℝ) * (Qn : ℝ) := by
    exact_mod_cast hDet
  have hPone : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (show 1 ≤ P by omega)
  have hPredR : (Qn : ℝ) - 1 < (Pn : ℝ) * σ := by
    nlinarith
  have hPredCast : (((Qn - 1 : ℕ) : ℝ)) = (Qn : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ Qn by omega)]
    norm_num
  have hR :
      (((Qn - 1 : ℕ) : ℝ)) < (((β Pn + 1 : ℕ) : ℝ)) := by
    rw [hPredCast]
    exact lt_trans hPredR (by simpa using (M Pn).2)
  have hN : Qn - 1 < β Pn + 1 := by exact_mod_cast hR
  omega

/-- upper bracket の next fraction は lower 側なので `β(Pn) ≥ Qn`。 -/
theorem nextQ_le_roof_nextP_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn) :
    Qn ≤ β Pn := by
  rcases B with ⟨hP, hPn, hNext, hCurrent, hDet⟩
  have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast hPn
  have hNextMul : (Qn : ℝ) < σ * (Pn : ℝ) :=
    (div_lt_iff₀ hPnR).1 hNext
  have hR : (Qn : ℝ) < (((β Pn + 1 : ℕ) : ℝ)) :=
    lt_trans hNextMul (by
      simpa [mul_comm] using (M Pn).2)
  have hN : Qn < β Pn + 1 := by exact_mod_cast hR
  omega

/--
lower inverse corridor の自然な全幅版。

`0 < k < Qn` なら `H(Q+k)=P+H(k)`。
`H(k)=Pn` となる最右端も、roof の超加法性で処理できる。
-/
theorem inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hkPos : 0 < k)
    (hk : k < Qn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  let H := M.inverse hσ k
  have hHPos : 0 < H := by
    dsimp [H]
    exact M.inverse_pos_of_pos hσ hkPos
  have hPredReach : k ≤ Qn - 1 := by omega
  have hNextReach : Qn - 1 ≤ β Pn :=
    M.nextQ_pred_le_roof_nextP_of_lowerFarey hσ B
  have hHLe : H ≤ Pn := by
    dsimp [H]
    exact M.inverse_le_of_reaches hσ (le_trans hPredReach hNextReach)
  have hBetaZero : β 0 = 0 := by
    rw [M.eq_natFloor' 0]
    simp
  have hBetaP : β P = Q := by
    have h := M.add_currentP_eq_add_Q_of_lowerFarey_sharp
      B (x := 0) B.2.1
    simpa [hBetaZero] using h
  have hReach : Q + k ≤ β (P + H) := by
    by_cases hHLt : H < Pn
    · have hShift := M.add_currentP_eq_add_Q_of_lowerFarey_sharp B hHLt
      rw [hShift]
      exact Nat.add_le_add_left (M.inverse_spec hσ k) Q
    · have hHEq : H = Pn := by omega
      rw [hHEq]
      have hSuper := M.add_le_add_roof P Pn
      rw [hBetaP] at hSuper
      omega
  have hUpper : M.inverse hσ (Q + k) ≤ P + H :=
    M.inverse_le_of_reaches hσ hReach
  have hLower : P + H ≤ M.inverse hσ (Q + k) := by
    by_contra hNot
    have hInvLt : M.inverse hσ (Q + k) < P + H := by omega
    have hInvSpec := M.inverse_spec hσ (Q + k)
    by_cases hAtMostP : M.inverse hσ (Q + k) ≤ P
    · have hMonoP := hMono hAtMostP
      rw [hBetaP] at hMonoP
      omega
    · have hPastP : P < M.inverse hσ (Q + k) := Nat.lt_of_not_ge hAtMostP
      let x := M.inverse hσ (Q + k) - P
      have hxPos : 0 < x := by dsimp [x]; omega
      have hPx : P + x = M.inverse hσ (Q + k) := by dsimp [x]; omega
      have hxLtH : x < H := by dsimp [x]; omega
      have hxLtPn : x < Pn := lt_of_lt_of_le hxLtH hHLe
      have hShift := M.add_currentP_eq_add_Q_of_lowerFarey_sharp B hxLtPn
      have hMinX : β x < k := M.inverse_min hσ hxLtH
      rw [← hPx, hShift] at hInvSpec
      omega
  exact Nat.le_antisymm hUpper hLower

/-- upper inverse corridor の positive residual 全幅版。 -/
theorem inverse_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn)
    (hkPos : 0 < k)
    (hk : k < Qn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  let H := M.inverse hσ k
  have hHPos : 0 < H := by
    dsimp [H]
    exact M.inverse_pos_of_pos hσ hkPos
  have hNextReach : Qn ≤ β Pn := M.nextQ_le_roof_nextP_of_upperFarey B
  have hHLe : H ≤ Pn := by
    dsimp [H]
    apply M.inverse_le_of_reaches hσ
    exact le_trans (Nat.le_of_lt hk) hNextReach
  have hBetaP : β P = Q - 1 := by
    rw [M.eq_natFloor' P]
    exact natFloor_currentP_eq_Q_sub_one_of_upperFarey B hPLt
  have hQPos : 0 < Q := by
    rcases B with ⟨hP, hPn, hNext, hCurrent, hDet⟩
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have hCurrentMul : σ * (P : ℝ) < (Q : ℝ) :=
      (lt_div_iff₀ hPR).1 hCurrent
    have hOneP : (P : ℝ) ≤ σ * (P : ℝ) := by
      simpa using
        (mul_le_mul_of_nonneg_right hσ (le_of_lt hPR))
    have hPQ : (P : ℝ) < (Q : ℝ) := lt_of_le_of_lt hOneP hCurrentMul
    have : (0 : ℝ) < (Q : ℝ) := lt_trans hPR hPQ
    exact_mod_cast this
  have hReach : Q + k ≤ β (P + H) := by
    by_cases hHLt : H < Pn
    · have hShift := M.add_currentP_eq_add_Q_of_upperFarey_sharp B hHPos hHLt
      rw [hShift]
      exact Nat.add_le_add_left (M.inverse_spec hσ k) Q
    · have hHEq : H = Pn := by omega
      rw [hHEq]
      have hSuper := M.add_le_add_roof P Pn
      rw [hBetaP] at hSuper
      omega
  have hUpper : M.inverse hσ (Q + k) ≤ P + H :=
    M.inverse_le_of_reaches hσ hReach
  have hLower : P + H ≤ M.inverse hσ (Q + k) := by
    by_contra hNot
    have hInvLt : M.inverse hσ (Q + k) < P + H := by omega
    have hInvSpec := M.inverse_spec hσ (Q + k)
    by_cases hAtMostP : M.inverse hσ (Q + k) ≤ P
    · have hMonoP := hMono hAtMostP
      rw [hBetaP] at hMonoP
      omega
    · have hPastP : P < M.inverse hσ (Q + k) := Nat.lt_of_not_ge hAtMostP
      let x := M.inverse hσ (Q + k) - P
      have hxPos : 0 < x := by dsimp [x]; omega
      have hPx : P + x = M.inverse hσ (Q + k) := by dsimp [x]; omega
      have hxLtH : x < H := by dsimp [x]; omega
      have hxLtPn : x < Pn := lt_of_lt_of_le hxLtH hHLe
      have hShift := M.add_currentP_eq_add_Q_of_upperFarey_sharp B hxPos hxLtPn
      have hMinX : β x < k := M.inverse_min hσ hxLtH
      rw [← hPx, hShift] at hInvSpec
      omega
  exact Nat.le_antisymm hUpper hLower

/-- lower inverse corridor は `k=0` も含め、自然 range `k<Qn` で一式になる。 -/
theorem inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp_including_zero
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn)
    (hk : k < Qn) :
    M.inverse hσ (Q + k) = P + M.inverse hσ k := by
  by_cases hk0 : k = 0
  · subst k
    simpa using M.inverse_currentQ_eq_currentP_of_lowerFarey hσ B hPLt
  · exact M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
      hσ hMono B (Nat.pos_of_ne_zero hk0) hk

/-- upper inverse corridor は `k=0` だけ endpoint correction `1` を持つ。 -/
theorem inverse_add_currentQ_eq_of_upperFarey_sharp_piecewise
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn)
    (hk : k < Qn) :
    M.inverse hσ (Q + k) =
      if k = 0 then P + 1 else P + M.inverse hσ k := by
  by_cases hk0 : k = 0
  · subst k
    simp only [add_zero, ↓reduceIte]
    exact M.inverse_currentQ_eq_currentP_add_one_of_upperFarey
      hσ hMono B hPLt
  · rw [ite_eq_right hk0]
    exact M.inverse_add_currentQ_eq_add_currentP_of_upperFarey_sharp
      hσ hMono B hPLt (Nat.pos_of_ne_zero hk0) hk

/-- lower corridor 内部の inverse bit は自然 range `k+1<Qn` で exact に反復する。 -/
theorem inverseStep_add_currentQ_eq_inverseStep_of_lowerFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hkPos : 0 < k)
    (hk : k + 1 < Qn) :
    M.inverseStep hσ (Q + k) = M.inverseStep hσ k := by
  have h0 := M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    hσ hMono B hkPos (by omega : k < Qn)
  have h1 := M.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    hσ hMono B (k := k + 1) (by omega) hk
  unfold inverseStep
  rw [show Q + k + 1 = Q + (k + 1) by omega]
  rw [h1, h0]
  omega

/-- upper corridor 内部の inverse bit も positive natural range で exact に反復する。 -/
theorem inverseStep_add_currentQ_eq_inverseStep_of_upperFarey_sharp
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (hMono : Monotone β)
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn)
    (hkPos : 0 < k)
    (hk : k + 1 < Qn) :
    M.inverseStep hσ (Q + k) = M.inverseStep hσ k := by
  have h0 := M.inverse_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    hσ hMono B hPLt hkPos (by omega : k < Qn)
  have h1 := M.inverse_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    hσ hMono B hPLt (k := k + 1) (by omega) hk
  unfold inverseStep
  rw [show Q + k + 1 = Q + (k + 1) by omega]
  rw [h1, h0]
  omega

end IsLowerMechanicalRoof
end Experimental2
end Collatz3
