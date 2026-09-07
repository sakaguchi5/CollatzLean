import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFirstDefectIndex24

set_option linter.style.nativeDecide false

/-!
# 第3例低枝探索 1: first defect の低14枝を幾何だけで固定する

高枝の有限排除から既に得た

* first defect index `j ≤ 24`,
* first defect は一セル,
* actual prefix height は strict に増加する,

という三事実を組み合わせる。

first defect の actual height を `a` とすると、一セル性から

  a = criticalHeight j - 1

である。また `j-1` までは critical roof 上にあり、actual height は strict に増えるため

  criticalHeight (j-1) < criticalHeight j - 1

が必要になる。

`j ≤ 24` の有限範囲でこの条件を kernel 計算すると、可能な `(j,a)` は正確に14組だけになる。
ここでは低枝を Collatz 整数の巨大な集合としてではなく、first-defect 幾何の14状態として固定する。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch

open DoubleDecomposition

/--
`j ≤ 24` に残る first-defect の `(index, actual height)` 14組。
height は後段の exact 2-adic valuation branch と一致する。
-/
def thirdExampleLow14FirstDefectPairs : List (Nat × Nat) :=
  [ (24, 37)
  , (23, 35)
  , (21, 32)
  , (19, 29)
  , (18, 27)
  , (16, 24)
  , (14, 21)
  , (12, 18)
  , (11, 16)
  , (9, 13)
  , (7, 10)
  , (6, 8)
  , (4, 5)
  , (2, 2)
  ]

/--
`j < 25` の有限範囲では、直前 roof より一つ上へ strict に入れる一セル位置は
上の14組に限られる。

ここは巨大 target に依存しない25状態の有限算術だけなので `decide` で閉じる。
-/
theorem thirdExample_low14_roof_pairs_checked :
    ∀ j : Fin 25,
      0 < j.val →
      Word.criticalHeight (j.val - 1) <
        Word.criticalHeight j.val - 1 →
      (j.val, Word.criticalHeight j.val - 1) ∈
        thirdExampleLow14FirstDefectPairs := by
  decide

/--
同じ actual height を持つ低14枝は一つしかない。
従って valuation `a` が決まれば first-defect index `j` も一意に決まる。
-/
theorem thirdExample_low14_height_determines_index
    {j₁ j₂ a : Nat}
    (h₁ : (j₁, a) ∈ thirdExampleLow14FirstDefectPairs)
    (h₂ : (j₂, a) ∈ thirdExampleLow14FirstDefectPairs) :
    j₁ = j₂ := by
  simp [thirdExampleLow14FirstDefectPairs] at h₁ h₂
  omega

/--
真の第3例 exact candidate の first defect は、低14枝のどれかに必ず入る。

これは単なる `a ≤ 37` より強く、`j` と `a` の対応まで保持する。
-/
theorem thirdExample_firstDefect_low14_pair
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    {j : Nat}
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    (j, Word.prefixTwoDepth w j) ∈ thirdExampleLow14FirstDefectPairs := by
  have hjLe := thirdExample_firstDefect_index_le_24 R CertL C F
  have hCell := thirdExampleFirstDefect_forced_oneCell C F
  have hCurrent := F.current_lt
  unfold Word.criticalDefect at hCell
  have hHeight :
      Word.prefixTwoDepth w j = Word.criticalHeight j - 1 := by
    omega
  have hjPos : 0 < j := by
    by_contra hNot
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hNot
    subst j
    simpa [Word.prefixTwoDepth, Word.criticalHeight] using F.current_lt
  have hPrev :=
    Word.prefixTwoDepth_lt_of_valid C.minimal.1
      (i := j - 1)
      (j := j)
      (by omega)
      (Nat.le_of_lt F.index_lt)
  rw [F.before (j - 1) (by omega), hHeight] at hPrev
  have hPair :=
    thirdExample_low14_roof_pairs_checked
      ⟨j, by omega⟩
      hjPos
      hPrev
  rw [← hHeight] at hPair
  exact hPair

/-- branch37 では first defect index は `j = 24` に固定される。 -/
theorem thirdExample_firstDefect_index_eq_24_of_height_eq_37
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    {j : Nat}
    (F : ThirdExampleFirstCriticalDefectAt w j)
    (h37 : Word.prefixTwoDepth w j = 37) :
    j = 24 := by
  have hPair := thirdExample_firstDefect_low14_pair R CertL C F
  rw [h37] at hPair
  simp [thirdExampleLow14FirstDefectPairs] at hPair
  omega

end Collatz2.CSTMicro.ThirdExampleSearch
