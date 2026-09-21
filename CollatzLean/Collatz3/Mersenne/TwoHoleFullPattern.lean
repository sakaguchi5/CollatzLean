import CollatzLean.Collatz3.Mersenne.SourceTargetTwoHoleProperResidualProof
import CollatzLean.Collatz3.Mersenne.SplitTwoHoleProperResidualProof

/-!
# Collatz3 Mersenne: three two-hole placements の full case 統合語彙

source / split / target の three placements を、exact equation の段階では
`TwoHoleWellFormedEquation`、full six-term certificate まで得た段階では
`TwoHoleFullCase` としてまとめる。

各 branch 固有の index や certificate は保持したまま、外部 arithmetic へ渡す境界だけを共通化する。
-/

namespace Collatz3
namespace Mersenne

/-- hole 2 の三配置を、必要な well-formed 条件込みでまとめた薄い和型。 -/
inductive TwoHoleWellFormedEquation
    (k n r L : ℕ) : Prop
  | source
      (a b : ℕ)
      (ha0 : 0 < a)
      (hab : a < b)
      (hbn : b < n)
      (hr : 0 < r)
      (hL : 0 < L)
      (hEq : SourceTwoHoleEquation k n r L a b)
  | split
      (a b : ℕ)
      (ha0 : 0 < a)
      (han : a < n)
      (hr : 0 < r)
      (hb0 : 0 < b)
      (hbL : b < L)
      (hEq : SplitTwoHoleEquation k n r L a b)
  | target
      (a b : ℕ)
      (hn : 0 < n)
      (hr : 0 < r)
      (ha0 : 0 < a)
      (hab : a < b)
      (hbL : b < L)
      (hEq : TargetTwoHoleEquation k n r L a b)

/-- 三配置の genuinely full six-term minimal certificate をまとめた薄い和型。 -/
inductive TwoHoleFullCase
    (k n r L : ℕ) : Prop
  | source
      (a b : ℕ)
      (ha0 : 0 < a)
      (hab : a < b)
      (hbn : b < n)
      (hr : 0 < r)
      (hL : 0 < L)
      (hEq : SourceTwoHoleEquation k n r L a b)
      (selected : Finset SourceTwoUnitIndex)
      (hCert : SourceTwoMinimalPatternCertificate k n r L a b selected)
      (hFull : SourceTwoFullPattern selected)
  | split
      (a b : ℕ)
      (ha0 : 0 < a)
      (han : a < n)
      (hr : 0 < r)
      (hb0 : 0 < b)
      (hbL : b < L)
      (hEq : SplitTwoHoleEquation k n r L a b)
      (selected : Finset SplitTwoUnitIndex)
      (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
      (hFull : SplitTwoFullPattern selected)
  | target
      (a b : ℕ)
      (hn : 0 < n)
      (hr : 0 < r)
      (ha0 : 0 < a)
      (hab : a < b)
      (hbL : b < L)
      (hEq : TargetTwoHoleEquation k n r L a b)
      (selected : Finset TargetTwoUnitIndex)
      (hCert : TargetTwoMinimalPatternCertificate k n r L a b selected)
      (hFull : TargetTwoFullPattern selected)

/--
`k≥3` の well-formed two-hole equation は、配置によらず full six-term case へ入る。
-/
theorem TwoHoleWellFormedEquation.exists_fullCase
    {k n r L : ℕ}
    (h : TwoHoleWellFormedEquation k n r L)
    (hk3 : 3 ≤ k) :
    TwoHoleFullCase k n r L := by
  rcases h with
    ⟨a, b, ha0, hab, hbn, hr, hL, hEq⟩ |
    ⟨a, b, ha0, han, hr, hb0, hbL, hEq⟩ |
    ⟨a, b, hn, hr, ha0, hab, hbL, hEq⟩
  · rcases hEq.largeDepth_exists_fullMinimalPattern
      hk3 ha0 hab hbn hr hL with ⟨selected, hCert, hFull⟩
    exact .source a b ha0 hab hbn hr hL hEq selected hCert hFull
  · rcases hEq.largeDepth_exists_fullMinimalPattern
      hk3 ha0 han hr hb0 hbL with ⟨selected, hCert, hFull⟩
    exact .split a b ha0 han hr hb0 hbL hEq selected hCert hFull
  · rcases hEq.largeDepth_exists_fullMinimalPattern
      hk3 hn hr ha0 hab hbL with ⟨selected, hCert, hFull⟩
    exact .target a b hn hr ha0 hab hbL hEq selected hCert hFull

/--
一般 `NondegenerateTwoThreeUnitExponentBound` だけでも、full six-term case の depth は
three placements 共通で一様有界になる。具体的な `k≤6` には後段の finite arithmetic が必要。
-/
theorem twoHoleFullCase_depth_bounded_of_twoThreeUnitBound
    (hSUnit : Arithmetic.NondegenerateTwoThreeUnitExponentBound) :
    ∃ K : ℕ,
      ∀ {k n r L : ℕ}, TwoHoleFullCase k n r L → k < K := by
  rcases hSUnit 6 with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n r L hFullCase
  rcases hFullCase with
    ⟨a, b, ha0, hab, hbn, hr, hL, hEq, selected, hCert, hFull⟩ |
    ⟨a, b, ha0, han, hr, hb0, hbL, hEq, selected, hCert, hFull⟩ |
    ⟨a, b, hn, hr, ha0, hab, hbL, hEq, selected, hCert, hFull⟩
  · apply hK (sourceTwoUnitTerm k n r L a b) selected k
    · have hSub : selected ⊆ (Finset.univ : Finset SourceTwoUnitIndex) := by simp
      have hCard := Finset.card_le_card hSub
      simpa [sourceTwoUnitIndex_card] using hCard
    · exact hCert.nondegenerate
    · refine ⟨SourceTwoUnitIndex.negThree, hCert.anchor_mem, ?_⟩
      rfl
  · apply hK (splitTwoUnitTerm k n r L a b) selected k
    · have hSub : selected ⊆ (Finset.univ : Finset SplitTwoUnitIndex) := by simp
      have hCard := Finset.card_le_card hSub
      simpa [splitTwoUnitIndex_card] using hCard
    · exact hCert.nondegenerate
    · refine ⟨SplitTwoUnitIndex.negThree, hCert.anchor_mem, ?_⟩
      rfl
  · apply hK (targetTwoUnitTerm k n r L a b) selected k
    · have hSub : selected ⊆ (Finset.univ : Finset TargetTwoUnitIndex) := by simp
      have hCard := Finset.card_le_card hSub
      simpa [targetTwoUnitIndex_card] using hCard
    · exact hCert.nondegenerate
    · refine ⟨TargetTwoUnitIndex.negThree, hCert.anchor_mem, ?_⟩
      rfl

end Mersenne
end Collatz3
