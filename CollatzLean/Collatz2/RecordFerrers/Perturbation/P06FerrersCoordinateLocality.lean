import CollatzLean.Collatz2.RecordFerrers.Perturbation.P05SpliceLocality
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockReplacement
import CollatzLean.Collatz2.Geometry.RankQuotient

/-!
# Record–Ferrers 摂動理論 6: block 外の Ferrers rank 座標

block replacement の外では chord rank が不変である。
FirstCrossing 同士なら、その整数 rank から residue / quotient の組も exact に不変となる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- fixed-chord point の residue / quotient Ferrers 座標。 -/
def rankFerrersCoordinate
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) : ℕ × ℕ :=
  (rankResidue x.word k, rankQuotient x.word k)

/--
compact-support block replacement の外では residue / quotient 座標が一致する。
proper cut の範囲で述べる。
-/
theorem rankFerrersCoordinate_eq_outside_replaced_block
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (hFu : FirstCrossing u.word)
    (hFv : FirstCrossing v.word)
    {k : ℕ}
    (hk : k < p)
    (hOutside : k ≤ start ∨ stop ≤ k) :
    rankFerrersCoordinate u k = rankFerrersCoordinate v k := by
  have hRankZ :=
    R.chordRankInt_outside (Nat.le_of_lt hk) hOutside
  by_cases hk0 : k = 0
  · subst k
    simp [rankFerrersCoordinate, rankResidue, rankQuotient, chordRank]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkU : k < oddSteps u.word := by
      rw [u.oddSteps_eq]
      exact hk
    have hkV : k < oddSteps v.word := by
      rw [v.oddSteps_eq]
      exact hk
    have hUZ := hFu.chordRankInt_eq_natCast hkPos hkU
    have hVZ := hFv.chordRankInt_eq_natCast hkPos hkV
    rw [hVZ, hUZ] at hRankZ
    have hRank : chordRank v.word k = chordRank u.word k := by
      exact_mod_cast hRankZ
    unfold rankFerrersCoordinate rankResidue rankQuotient
    rw [hRank, u.oddSteps_eq, v.oddSteps_eq]

end RecordFerrers
end Collatz2
