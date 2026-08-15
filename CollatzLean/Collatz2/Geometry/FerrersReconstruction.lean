import CollatzLean.Collatz2.Geometry.ResidueIndexedFerrers
import CollatzLean.Collatz2.Geometry.CriticalProfile
import CollatzLean.Collatz2.Core.TranslationPath

/-!
# Collatz2 Geometry: Ferrers reconstruction

full rank/Ferrers profile は、global chord `(p,H)` と合わせれば valid FirstCrossing word の
complete invariant になる。ここでは cut-indexed coordinate から始め、primitive case の
residue-indexed quotient profile へ持ち上げる。
-/

namespace Collatz2
namespace Word

/-- cut `k` の lossless rank/Ferrers coordinate。 -/
def ferrersCoordinate (w : Word) (k : ℕ) : ℕ × ℕ :=
  (rankResidue w k, rankQuotient w k)

/-- 同じ denominator と Ferrers coordinate は chord rank を一致させる。 -/
theorem chordRank_eq_of_ferrersCoordinate_eq
    {u v : Word}
    (hp : oddSteps u = oddSteps v)
    {k : ℕ}
    (hCoord : ferrersCoordinate u k = ferrersCoordinate v k) :
    chordRank u k = chordRank v k := by
  have hr : rankResidue u k = rankResidue v k := by
    exact congrArg Prod.fst hCoord
  have hq : rankQuotient u k = rankQuotient v k := by
    exact congrArg Prod.snd hCoord
  rw [chordRank_eq_rankResidue_add_oddSteps_mul_rankQuotient,
      chordRank_eq_rankResidue_add_oddSteps_mul_rankQuotient,
      hr, hq, hp]

/-- same chord + same rank coordinate なら proper prefix depth も同じ。 -/
theorem prefixTwoDepth_eq_of_same_ferrersCoordinate
    {u v : Word}
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLtU : k < oddSteps u)
    (hCoord : ferrersCoordinate u k = ferrersCoordinate v k) :
    prefixTwoDepth u k = prefixTwoDepth v k := by
  have hkLtV : k < oddSteps v := by
    rw [← hp]
    exact hkLtU
  have hRank := chordRank_eq_of_ferrersCoordinate_eq hp hCoord
  have hZu := hFu.chordRankInt_eq_natCast hkPos hkLtU
  have hZv := hFv.chordRankInt_eq_natCast hkPos hkLtV
  have hRankZ : chordRankInt u k = chordRankInt v k := by
    rw [hZu, hZv, hRank]
  unfold chordRankInt at hRankZ
  rw [hH, hp] at hRankZ
  have hpPos : 0 < oddSteps v := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hFv.nonempty
  have hpPosZ : 0 < (oddSteps v : ℤ) := by
    exact_mod_cast hpPos
  have hDepthZ :
      (prefixTwoDepth u k : ℤ) = (prefixTwoDepth v k : ℤ) := by
    nlinarith
  exact_mod_cast hDepthZ

/-- full cut-indexed Ferrers profile は exact affine translation `B` も復元する。 -/
theorem affineConst_eq_of_same_ferrersProfile
    {u v : Word}
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hProfile :
      ∀ k : ℕ, k < oddSteps u →
        ferrersCoordinate u k = ferrersCoordinate v k) :
    affineConst u = affineConst v := by
  rw [← affinePathSum_eq_affineConst u,
      ← affinePathSum_eq_affineConst v]
  unfold affinePathSum
  apply Finset.sum_congr
  · rw [hp]
  · intro k hk
    have hkLtV : k < oddSteps v :=
      Finset.mem_range.mp hk
    have hkLtU : k < oddSteps u := by
      rw [hp]
      exact hkLtV
    by_cases hk0 : k = 0
    · subst k
      simp [affinePathTerm, prefixTwoDepth, hp]
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      have hDepth :=
        prefixTwoDepth_eq_of_same_ferrersCoordinate
          hFu hFv hp hH hkPos hkLtU (hProfile k hkLtU)
      unfold affinePathTerm
      rw [hDepth, hp]

/-- full cut-indexed Ferrers profile は valid FirstCrossing word の complete invariant。 -/
theorem word_eq_of_same_ferrersProfile
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hProfile :
      ∀ k : ℕ, k < oddSteps u →
        ferrersCoordinate u k = ferrersCoordinate v k) :
    u = v := by
  have hB :=
    affineConst_eq_of_same_ferrersProfile hFu hFv hp hH hProfile
  exact valid_word_unique_of_oddSteps_twoSteps_affineConst
    hu hv hp hH hB

/-- same `(p,H)` なら proper cut の rank residue 自体は deterministic。 -/
theorem rankResidue_eq_of_same_exponentPair
    {u v : Word}
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLtU : k < oddSteps u) :
    rankResidue u k = rankResidue v k := by
  have hkLtV : k < oddSteps v := by
    rw [← hp]
    exact hkLtU
  rw [hFu.rankResidue_eq_stripRank_mod hkPos hkLtU,
      hFv.rankResidue_eq_stripRank_mod hkPos hkLtV]
  unfold stripRank
  rw [hH, hp]

/--
primitive caseでは residue-indexed quotient profile と `(p,H)` だけで word を復元できる。
-/
theorem word_eq_of_same_residueIndexedFerrersProfile
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hcopU : Nat.Coprime (twoSteps u) (oddSteps u))
    (hcopV : Nat.Coprime (twoSteps v) (oddSteps v))
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hProfile :
      ∀ r : ℕ, r < oddSteps u →
        residueRankQuotientProfile hFu hcopU r =
          residueRankQuotientProfile hFv hcopV r) :
    u = v := by
  apply word_eq_of_same_ferrersProfile hu hv hFu hFv hp hH
  intro k hkLtU
  by_cases hk0 : k = 0
  · subst k
    simp [ferrersCoordinate]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkLtV : k < oddSteps v := by
      rw [← hp]
      exact hkLtU
    have hRes :=
      rankResidue_eq_of_same_exponentPair hFu hFv hp hH hkPos hkLtU
    have hrLt : rankResidue u k < oddSteps u :=
      hFu.rankResidue_lt_oddSteps
    have hProf := hProfile (rankResidue u k) hrLt
    have hQu :=
      residueRankQuotientProfile_rankResidue_eq
        hFu hcopU hkPos hkLtU
    have hQv :=
      residueRankQuotientProfile_rankResidue_eq
        hFv hcopV hkPos hkLtV
    have hQ : rankQuotient u k = rankQuotient v k := by
      calc
        rankQuotient u k
            = residueRankQuotientProfile hFu hcopU (rankResidue u k) := hQu.symm
        _ = residueRankQuotientProfile hFv hcopV (rankResidue u k) := hProf
        _ = residueRankQuotientProfile hFv hcopV (rankResidue v k) := by rw [hRes]
        _ = rankQuotient v k := hQv
    unfold ferrersCoordinate
    rw [hRes, hQ]

end Word
end Collatz2
