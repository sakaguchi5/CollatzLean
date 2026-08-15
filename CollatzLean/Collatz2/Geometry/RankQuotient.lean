import CollatzLean.Collatz2.Geometry.RankStrip

/-!
# Collatz2 Geometry: rank residue / quotient decomposition

FirstCrossing proper cut の chord rank

  d_k = H*k - p*h_k

を、modulo `p` の residue と `p`-quotient に分ける。

既存の strip decomposition

  d_k = stripRank(k) + p*extraDepth(k)

に対して stripRank 自身を `p` で割ることで

  d_k = rankResidue(k) + p*rankQuotient(k)

  rankResidue(k) = stripRank(k) % p
  rankQuotient(k) = stripRank(k) / p + extraDepth(k)

を exact に保持する。

`rankQuotient` は deterministic な strip wrap と word 固有の extra depth の和であり、
reduced / nonreduced の両方を original word 上で同じ座標に置く。
-/

namespace Collatz2
namespace Word

/-- chord rank の modulo `p` residue。 -/
def rankResidue (w : Word) (k : ℕ) : ℕ :=
  chordRank w k % oddSteps w

/-- chord rank の `p`-quotient。 -/
def rankQuotient (w : Word) (k : ℕ) : ℕ :=
  chordRank w k / oddSteps w

@[simp] theorem rankResidue_zero (w : Word) :
    rankResidue w 0 = 0 := by
  simp [rankResidue, chordRank, prefixTwoDepth]

@[simp] theorem rankQuotient_zero (w : Word) :
    rankQuotient w 0 = 0 := by
  simp [rankQuotient, chordRank, prefixTwoDepth]

/-- Stage 2a: proper cut の rank residue は strip residue と同じ。 -/
theorem FirstCrossing.rankResidue_eq_stripRank_mod
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    rankResidue w k = stripRank w k % oddSteps w := by
  have hDecomp :=
    hF.chordRank_eq_stripRank_add_extraDepth hkPos hkLt
  unfold rankResidue
  rw [hDecomp]
  exact Nat.add_mul_mod_self_left _ _ _

/-- Stage 2b: proper FirstCrossing rank quotient は strip wrap + extra depth。 -/
theorem FirstCrossing.rankQuotient_eq_stripDiv_add_extraDepth
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    rankQuotient w k =
      stripRank w k / oddSteps w + extraDepth w k := by
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  have hDecomp :=
    hF.chordRank_eq_stripRank_add_extraDepth hkPos hkLt
  unfold rankQuotient
  rw [hDecomp]
  exact Nat.add_mul_div_left _ _ hpPos

/--
Stage 1: chord rank の exact quotient/residue decomposition。

  d_k = residue_k + p * quotient_k.
-/
theorem chordRank_eq_rankResidue_add_oddSteps_mul_rankQuotient
    (w : Word)
    (k : ℕ) :
    chordRank w k =
      rankResidue w k + oddSteps w * rankQuotient w k := by
  simpa [rankResidue, rankQuotient] using
    (Nat.mod_add_div (chordRank w k) (oddSteps w)).symm

/-- proper FirstCrossing rank residue は `p` 未満。 -/
theorem FirstCrossing.rankResidue_lt_oddSteps
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ} :
    rankResidue w k < oddSteps w := by
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  unfold rankResidue
  exact Nat.mod_lt _ hpPos

/--
wide strip は original rank quotient を正にする。
したがって descendant pair へ移らなくても original weighted term に半減層が一つ以上残る。
-/
theorem FirstCrossing.rankQuotient_pos_of_stripRank_gt_oddSteps
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w)
    (hWide : oddSteps w < stripRank w k) :
    0 < rankQuotient w k := by
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  have hDivPos : 0 < stripRank w k / oddSteps w := by
    have hOne : 1 ≤ stripRank w k / oddSteps w :=
      (Nat.le_div_iff_mul_le hpPos).2 (by
        simpa using Nat.le_of_lt hWide)
    omega
  rw [hF.rankQuotient_eq_stripDiv_add_extraDepth hkPos hkLt]
  omega

/-- rank residue の ZMod cast は従来の chord-rank residue と一致する。 -/
theorem rankResidue_cast_eq_chordRankResidue
    {w : Word}
    (k : ℕ) :
    ((rankResidue w k : ℕ) : ZMod (oddSteps w)) =
      chordRankResidue w k := by
  unfold rankResidue chordRankResidue
  simp

/--
`k=0` を含む全 cut `k<p` で rank residue は modulo `p` 上 `H*k` と一致する。
-/
theorem FirstCrossing.rankResidue_cast_eq_twoSteps_mul
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkLt : k < oddSteps w) :
    ((rankResidue w k : ℕ) : ZMod (oddSteps w)) =
      ((twoSteps w * k : ℕ) : ZMod (oddSteps w)) := by
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    calc
      ((rankResidue w k : ℕ) : ZMod (oddSteps w))
          = chordRankResidue w k :=
            rankResidue_cast_eq_chordRankResidue k
      _ = ((twoSteps w * k : ℕ) : ZMod (oddSteps w)) :=
            hF.chordRankResidue_eq hkPos hkLt

end Word
end Collatz2
