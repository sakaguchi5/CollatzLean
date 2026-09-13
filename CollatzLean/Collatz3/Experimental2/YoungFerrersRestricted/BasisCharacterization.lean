import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisParity

/-!
# Collatz3 Experimental2: basis equality と対角 corner の非同時性

Frobenius arm `a_i` と leg `b_i = a_i - s_i` はともに strict に減少する。
隣接位置で

* arm が最小の1だけ落ちる、または
* leg が最小の1だけ落ちる

ことを要求すると、横・縦の「余分な corner」が同じ対角段で同時には起きない。
terminal では arm または leg のどちらかが0へ到達する。

この条件が basis recurrence の equality case と exact に一致することを証明する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/--
basis equality を特徴付ける「対角で余分な horizontal/vertical corner が同時に起きない」条件。

隣接 step では

* `a = b + 1` なら arm 側が最小 gap、
* `a = b + 1 + s - t` なら leg 側が最小 gap

である。
-/
inductive NoSimultaneousDiagonalCorner : List ℤ → List ℤ → Prop
  | nil : NoSimultaneousDiagonalCorner [] []
  | single
      (s a : ℤ)
      (terminal : a = 0 ∨ a = s) :
      NoSimultaneousDiagonalCorner [s] [a]
  | cons
      {s t : ℤ}
      {ss : List ℤ}
      {a b : ℤ}
      {as : List ℤ}
      (tail : NoSimultaneousDiagonalCorner (t :: ss) (b :: as))
      (tight : a = b + 1 ∨ a = b + 1 + s - t) :
      NoSimultaneousDiagonalCorner (s :: t :: ss) (a :: b :: as)

/-- canonical basis arm は no-simultaneous-corner 条件を満たす。 -/
theorem basisArms_noSimultaneousDiagonalCorner :
    ∀ ranks : List ℤ,
      NoSimultaneousDiagonalCorner ranks (basisArms ranks)
  | [] => NoSimultaneousDiagonalCorner.nil
  | [s] => by
      by_cases hs : s ≤ 0
      · simpa [basisArms, hs] using
          NoSimultaneousDiagonalCorner.single s 0 (Or.inl rfl)
      · simpa [basisArms, hs] using
          NoSimultaneousDiagonalCorner.single s s (Or.inr rfl)
  | s :: t :: ss => by
      have hTail := basisArms_noSimultaneousDiagonalCorner (t :: ss)
      have hLen := basisArms_length (t :: ss)
      cases hBasis : basisArms (t :: ss) with
      | nil =>
          simp [hBasis] at hLen
      | cons b as =>
          rw [hBasis] at hTail
          by_cases hst : s ≤ t
          · simpa [basisArms, hBasis, hst] using
              NoSimultaneousDiagonalCorner.cons hTail (Or.inl rfl)
          · simpa [basisArms, hBasis, hst] using
              NoSimultaneousDiagonalCorner.cons hTail (Or.inr rfl)

/--
任意 realization では、basis arm と一致することと no-simultaneous-corner 条件が同値。
-/
theorem arms_eq_basisArms_iff_noSimultaneousDiagonalCorner
    {ranks arms : List ℤ}
    (hReal : IsArmRealization ranks arms) :
    arms = basisArms ranks ↔
      NoSimultaneousDiagonalCorner ranks arms := by
  constructor
  · intro hEq
    subst arms
    exact basisArms_noSimultaneousDiagonalCorner ranks
  · intro hCorner
    induction hReal with
    | nil =>
        rfl
    | single s a ha0 hleg =>
        cases hCorner with
        | single _ _ hterm =>
            by_cases hs : s ≤ 0
            · have ha : a = 0 := by
                rcases hterm with ha | ha
                · exact ha
                · omega
              simp [basisArms, hs, ha]
            · have hspos : 0 < s := lt_of_not_ge hs
              have ha : a = s := by
                rcases hterm with ha | ha
                · omega
                · exact ha
              simp [basisArms, hs, ha]
    | @cons s t ss a b as hTail ha0 hleg hArm hLeg ih =>
        cases hCorner with
        | cons hCornerTail hTight =>
            have hTailEq := ih hCornerTail
            have hBasisLen := basisArms_length (t :: ss)
            rw [← hTailEq] at hBasisLen
            have hGet : (basisArms (t :: ss)).getD 0 0 = b := by
              rw [← hTailEq]
              simp
            by_cases hst : s ≤ t
            · have ha : a = b + 1 := by
                rcases hTight with hTight | hTight
                · exact hTight
                · omega
              rw [basisArms_cons_cons, hGet]
              rw [ite_eq_left hst]
              rw [← hTailEq]
              simp [ha]
            · have hts : t < s := lt_of_not_ge hst
              have ha : a = b + 1 + s - t := by
                rcases hTight with hTight | hTight
                · omega
                · exact hTight
              rw [basisArms_cons_cons, hGet]
              rw [ite_eq_right hst]
              rw [← hTailEq]
              simp [ha]

/-- F7 の abstract equality characterization。 -/
theorem symbolWeightZ_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner
    {ranks arms : List ℤ}
    (hReal : IsArmRealization ranks arms) :
    symbolWeightZ ranks arms = basisWeightZ ranks ↔
      NoSimultaneousDiagonalCorner ranks arms := by
  rw [symbolWeightZ_eq_basisWeightZ_iff hReal]
  exact arms_eq_basisArms_iff_noSimultaneousDiagonalCorner hReal

/--
F7: actual Young 図形が successive-rank basis の最小面積を達成することと、
Frobenius 対角上で horizontal / vertical の余分な corner が同時発生しないことは同値。
-/
theorem codeArea_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner
    (c : WidthDropCode) :
    (codeArea c : ℤ) = basisWeightZ (successiveRankVector c) ↔
      NoSimultaneousDiagonalCorner
        (successiveRankVector c)
        (frobeniusArmsZ c) := by
  rw [← frobeniusSymbolWeight_eq_codeArea c]
  exact
    symbolWeightZ_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner
      (frobeniusVectors_realize c)

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/--
RecordFerrers 版の F7。
rank-envelope Young 図形が basis 面積を exact に達成することと、
その Frobenius 対角で余分な horizontal / vertical corner が同時発生しないことが同値。
-/
theorem youngCellCount_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    (R.youngCellCount : ℤ) = basisWeightZ R.successiveRanks ↔
      NoSimultaneousDiagonalCorner
        R.successiveRanks
        (frobeniusArmsZ R.plateauWidthDropCode) := by
  unfold youngCellCount successiveRanks
  exact
    codeArea_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner
      R.plateauWidthDropCode

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
