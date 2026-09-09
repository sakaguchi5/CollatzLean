import CollatzLean.Collatz3.Experimental.PromotedLocalLemmas

/-!
# Collatz3 experimental: 昇格局所補題の既存主定理への適用

`PromotedLocalLemmas` で名前を与えた局所 theorem が、既存の長い結果を
どこまで短い corollary として再構成できるかを確認する。

元 theorem は regression 用に残し、ここでは同じ statement を `_via_...` の名前で再証明する。
`Experimental2` ではこの短い依存形を採用する想定。
-/

namespace Collatz3
namespace Experimental

namespace HasUnitCarry

/-- residual の反復下側評価は、residual 自身の unit-carry 性から既存 `mul_lower` を再利用できる。 -/
theorem residual_mul_lower_via_normalization
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (k r : ℕ) :
    k * roofResidual β r ≤ roofResidual β (k * r) := by
  have Ures : HasUnitCarry (roofResidual β) := U.residual_hasUnitCarry
  simpa using Ures.mul_lower k r

/-- residual の sharp 上側反復評価も既存 `mul_upper_succ` の再利用で済む。 -/
theorem residual_mul_upper_succ_via_normalization
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (k r : ℕ) :
    roofResidual β ((k + 1) * r) ≤
      (k + 1) * roofResidual β r + k := by
  have Ures : HasUnitCarry (roofResidual β) := U.residual_hasUnitCarry
  simpa using Ures.mul_upper_succ k r

end HasUnitCarry

/--
local failure exact law を roof-slack 保存式から再構成した版。

長い証明の本質が
`localDepth + slack = β(j) + carry`
と `carry ≤ 1` だけであることを明示する。
-/
theorem localFailure_iff_roofReturn_and_carryOne_via_roofSlack
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a j : ℕ}
    (hStartRoof : IsRoofCut β m height a)
    (hEndLt : a + j < m) :
    β j < localDepth height a j ↔
      IsRoofCut β m height (a + j) ∧
        roofCarry β a j = 1 := by
  have hExact :=
    U.localDepth_add_roofSlack_eq_blockDepth_add_carry
      A hStartRoof.2.2 hEndLt
  have hEndLe : height (a + j) ≤ β (a + j) :=
    A.1 (a + j) hEndLt
  have hSlackIff :=
    roofSlack_eq_zero_iff_of_le hEndLe
  have hCarryLe := U.carry_le_one a j
  constructor
  · intro hFail
    have hCarryOne : roofCarry β a j = 1 := by
      omega
    have hSlackZero : roofSlack β height (a + j) = 0 := by
      omega
    have hEndEq : height (a + j) = β (a + j) :=
      hSlackIff.mp hSlackZero
    have haPos : 0 < a := hStartRoof.1
    have hEndPos : 0 < a + j :=
      lt_of_lt_of_le haPos (Nat.le_add_right a j)
    refine ⟨?_, hCarryOne⟩
    exact ⟨hEndPos, hEndLt, hEndEq⟩
  · rintro ⟨hEndRoof, hCarryOne⟩
    have hSlackZero : roofSlack β height (a + j) = 0 :=
      hSlackIff.mpr hEndRoof.2.2
    omega

/-- terminal minimality exact law を terminal depth 数値化から一行算術へ落とした版。 -/
theorem terminalMinimal_iff_carryZero_via_exactDepth
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (hStartRoof : IsRoofCut β m height a)
    (hTerminal : a + r = m) :
    localDepth height a r = criticalDepth β r ↔
      roofCarry β a r = 0 := by
  have hExact :=
    U.terminalLocalDepth_eq_criticalDepth_add_carry
      A hStartRoof hTerminal
  omega

namespace HasUnitCarry

/-- normalized Record 型 carry budget を一般 anchor-budget theorem から導いた版。 -/
theorem normalizedFactorization_carrySum_eq_length_sub_one_via_genericBudget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (rs : List ℕ)
    (hCover : m = 1 + rs.sum)
    (hFactor :
      β m = (rs.map β).sum + rs.length) :
    (carryListFrom β 1 rs).sum = rs.length - 1 := by
  have hBudget :=
    U.factorization_anchor_add_carrySum_eq_budget
      (a := 1) (K := rs.length) rs hCover hFactor
  rw [hOne] at hBudget
  omega

/--
leaf 数で書いた maximal refinement budget から、全内部 carry `1` を導く版。

`internalCount + 1 = leaves.length` を使うため、Record の cut 数との接続が読みやすい。
-/
theorem refinement_all_internalCarries_one_of_leafBudget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (t : WidthRefinement)
    (hMax :
      (t.internalCarries β).sum = t.leaves.length - 1) :
    t.internalCarries β =
      List.replicate (t.leaves.length - 1) 1 := by
  have hCount := WidthRefinement.internalCount_add_one_eq_leaves_length t
  have hMaxCount :
      (t.internalCarries β).sum = t.internalCount := by
    omega
  have hAll :=
    U.refinement_all_internalCarries_one_of_maximal t hMaxCount
  have hCountEq : t.internalCount = t.leaves.length - 1 := by
    omega
  simpa [hCountEq] using hAll

end HasUnitCarry

/-- homogenized slope 一意性を有限距離補題 + 純粋 Archimedean 終了補題から再構成した版。 -/
theorem homogenizedSlope_unique_via_distance
    {β : ℕ → ℕ}
    {ρ σ : ℝ}
    (Sρ : IsHomogenizedSlope β ρ)
    (Sσ : IsHomogenizedSlope β σ) :
    ρ = σ := by
  apply eq_of_mutual_le_add_inv_nat
  intro n hn
  exact homogenizedSlope_distance_le_inv Sρ Sσ hn

namespace HasUnitCarry

/-- rational lower closed form を scaled-cell Nat 除算補題で再構成した版。 -/
theorem rationalLower_residual_eq_div_via_scaledCell
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : roofResidual β q = p) :
    ∀ n : ℕ,
      roofResidual β n = lowerRationalResidual p q n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [lowerRationalResidual, U.roofResidual_zero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hWindow := S.2 n hnPos
    have hStrict :=
      U.rationalLower_strictUpper S hCoprime hLower hnPos
    unfold lowerRationalResidual
    symm
    apply natDiv_eq_of_scaledLowerCell
    · simpa [Nat.mul_comm] using hWindow.1
    · simpa [Nat.mul_comm] using hStrict

/-- rational upper closed form を scaled upper-cell Nat 除算補題で再構成した版。 -/
theorem rationalUpper_residual_eq_sub_one_div_via_scaledCell
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : roofResidual β q + 1 = p) :
    ∀ n : ℕ,
      roofResidual β n = upperRationalResidual p q n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [upperRationalResidual, U.roofResidual_zero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hWindow := S.2 n hnPos
    have hStrict :=
      U.rationalUpper_strictLower S hCoprime hUpper hnPos
    unfold upperRationalResidual
    symm
    apply natSubOneDiv_eq_of_scaledUpperCell
    · simpa [Nat.mul_comm] using hStrict
    · simpa [Nat.mul_comm] using hWindow.2

end HasUnitCarry

end Experimental
end Collatz3
