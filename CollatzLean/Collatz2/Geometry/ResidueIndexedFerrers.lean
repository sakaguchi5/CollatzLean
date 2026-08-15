import CollatzLean.Collatz2.Geometry.WeightedRankBaseline

/-!
# Collatz2 Geometry: residue-indexed Ferrers profile

primitive FirstCrossing では rank residue map は `0,...,p-1` の permutation である。
その逆写像を `residueCut` として選び、cut-indexed quotient を

  q_r := rankQuotient(residueCut(r))

へ移す。

これにより path の weighted 情報を cut index ではなく residue-indexed depth profile
`q_r` として保持できる。
-/

namespace Collatz2
namespace Word

/-- primitive rank residue permutation の finite inverse selector。 -/
noncomputable def residueCut
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    (r : ℕ) : ℕ := by
  classical
  if hrLt : r < oddSteps w then
    if hr0 : r = 0 then
      exact 0
    else
      exact Classical.choose
        (hF.exists_unique_proper_cut_of_rankResidue
          hcop (Nat.pos_of_ne_zero hr0) hrLt).exists
  else
    exact 0

/-- positive proper residue に対応する cut の specification。 -/
theorem residueCut_spec
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < oddSteps w) :
    0 < residueCut hF hcop r ∧
      residueCut hF hcop r < oddSteps w ∧
      rankResidue w (residueCut hF hcop r) = r := by
  classical
  have hr0 : r ≠ 0 := Nat.ne_of_gt hrPos
  have hSpec :=
    Classical.choose_spec
      (hF.exists_unique_proper_cut_of_rankResidue hcop hrPos hrLt).exists
  simpa [residueCut, hrLt, hr0] using hSpec

/-- residue 0 の inverse cut は 0。 -/
@[simp] theorem residueCut_zero
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    residueCut hF hcop 0 = 0 := by
  classical
  simp [residueCut]

/-- proper cut は自分の residue から一意に復元される。 -/
theorem residueCut_rankResidue_eq_cut
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    residueCut hF hcop (rankResidue w k) = k := by
  have hrLt : rankResidue w k < oddSteps w :=
    hF.rankResidue_lt_oddSteps
  have hrNe : rankResidue w k ≠ 0 :=
    hF.rankResidue_ne_zero_of_coprime hcop hkPos hkLt
  have hrPos : 0 < rankResidue w k := Nat.pos_of_ne_zero hrNe
  have hChosen := residueCut_spec hF hcop hrPos hrLt
  obtain ⟨x, hx, hUnique⟩ :=
    hF.exists_unique_proper_cut_of_rankResidue hcop hrPos hrLt
  have hChosenEq : residueCut hF hcop (rankResidue w k) = x :=
    hUnique _ hChosen
  have hkEq : k = x :=
    hUnique _ ⟨hkPos, hkLt, rfl⟩
  exact hChosenEq.trans hkEq.symm

/-- residue-indexed quotient-depth profile `q_r`。 -/
noncomputable def residueRankQuotientProfile
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    (r : ℕ) : ℕ :=
  rankQuotient w (residueCut hF hcop r)

@[simp] theorem residueRankQuotientProfile_zero
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    residueRankQuotientProfile hF hcop 0 = 0 := by
  simp [residueRankQuotientProfile]

/--
3. proper cut の quotient は residue-indexed profile を読むだけで完全に復元できる。
-/
theorem residueRankQuotientProfile_rankResidue_eq
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    residueRankQuotientProfile hF hcop (rankResidue w k) =
      rankQuotient w k := by
  unfold residueRankQuotientProfile
  rw [residueCut_rankResidue_eq_cut hF hcop hkPos hkLt]

/-- residue-indexed weighted term。 -/
noncomputable def residueIndexedFerrersWeight
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    (r : ℕ) : ZMod (terminalGap w) :=
  inverseUnitValue R ^ r *
    halfUnitValue R ^ residueRankQuotientProfile hF hcop r

/-- proper cut の inverse rank weight は対応する residue-indexed term と一致。 -/
theorem RankUnitData.inverseRankWeight_eq_residueIndexedFerrersWeight
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    inverseRankWeight R k =
      residueIndexedFerrersWeight R hF hcop (rankResidue w k) := by
  rw [R.inverseRankWeight_eq_baseResidueWeight_mul_halfUnitValue_pow]
  unfold baseResidueWeight residueIndexedFerrersWeight inverseUnitValue
  rw [residueRankQuotientProfile_rankResidue_eq hF hcop hkPos hkLt]

end Word
end Collatz2
