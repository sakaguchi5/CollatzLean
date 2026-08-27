import CollatzLean.Collatz2.RecordFerrers.Perturbation.P33BooleanFerrersOrderEmbedding

/-!
# Record–Ferrers 摂動理論 34: 標準境界削除の actual Ferrers 変形

P32 では一つの内部 Record 境界を消す操作を Boolean pattern 上で定義し、
P33 ではその下向き順序が標準平坦代表の Ferrers inclusion と exact に一致することを示した。

本ファイルでは、この一段削除を実際の fixed-chord Ferrers 変形へ持ち上げる。

cut 1 から始まる二つの genuine RecordDecomposition は、cut 0, 1, terminal で
height が一致する。従って両者の間には区間 `[1,p]` を support とする
`BlockReplacement` が存在する。

これを P30–P33 の標準平坦 family に適用すると、一境界削除は

* actual `BlockReplacement`
* source / target とも FirstCrossing
* Ferrers inclusion では strict downward

を同時に満たす genuine deformation になる。

局所 support を「削除した境界の直前・直後の保持境界」まで縮める問題は、
この global actualization の次段に分離する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. cut 1 標準分解どうしの global replacement -/

/--
cut 1 から genuine RecordDecomposition を持つ同一 fixed-fiber の二点は、
区間 `[1,p]` 上の `BlockReplacement` で結ばれる。

区間外で確認すべき cut は 0, 1, p だけである。
cut 1 では両分解の左端が critical roof 上にあり、0 と p は fixed fiber から自動一致する。
-/
theorem blockReplacement_one_terminal_of_recordDecompositions
    {p H : ℕ}
    {x y : FiberPoint p H}
    (Dx : RecordDecomposition x 1)
    (Dy : RecordDecomposition y 1) :
    BlockReplacement x y 1 p := by
  have hSumPos : 0 < Dx.lengths.sum := Dx.chain.sum_pos
  have hTerminal : 1 + Dx.lengths.sum = p :=
    Dx.chain.start_add_sum_eq_terminal
  have hpGt : 1 < p := by omega
  have hxRoof : x.height 1 = criticalHeight 1 := by
    have h := Dx.chain.startRoof
    unfold RoofContact at h
    exact h
  have hyRoof : y.height 1 = criticalHeight 1 := by
    have h := Dy.chain.startRoof
    unfold RoofContact at h
    exact h
  refine {
    start_lt_stop := hpGt
    stop_le_terminal := le_rfl
    outside := ?_
  }
  intro k hkp hOutside
  rcases hOutside with hkLeft | hkRight
  · have hkCases : k = 0 ∨ k = 1 := by omega
    rcases hkCases with rfl | rfl
    · unfold profileDisplacement
      simp
    · unfold profileDisplacement
      rw [hxRoof, hyRoof]
      ring
  · have hkEq : k = p := by omega
    subst k
    unfold profileDisplacement
    simp

/-! ## 2. 標準平坦 family への適用 -/

/--
任意の二つの Boolean pattern の標準平坦代表は、区間 `[1,p]` の actual replacement で結ばれる。
順序仮定は不要である。
-/
theorem canonicalFlatPoint_blockReplacement_one_terminal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    BlockReplacement
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (canonicalFlatPoint P hPrimitive hReduced u D S)
      1 P.oddCount := by
  obtain ⟨ER, _⟩ :=
    exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D R
  obtain ⟨ES, _⟩ :=
    exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D S
  exact blockReplacement_one_terminal_of_recordDecompositions ER ES

/--
Boolean 順序で下側へ進む標準平坦代表は、actual replacement でも結ばれる。
-/
theorem canonicalFlatPoint_actual_downward_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    BlockReplacement
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (canonicalFlatPoint P hPrimitive hReduced u D S)
        1 P.oddCount ∧
      FirstCrossing
        (canonicalFlatPoint P hPrimitive hReduced u D S).word ∧
      FiberPoint.FerrersLe
        (canonicalFlatPoint P hPrimitive hReduced u D S)
        (canonicalFlatPoint P hPrimitive hReduced u D R) := by
  refine ⟨canonicalFlatPoint_blockReplacement_one_terminal
      P hPrimitive hReduced u D R S, ?_, ?_⟩
  · unfold canonicalFlatPoint
    exact canonicalFlatRepresentative_firstCrossing
      P hPrimitive hReduced u D S
  · exact canonicalFlatPoint_ferrersLe_of_retainedLe
      P hPrimitive hReduced u D hSR

/-! ## 3. 一境界削除を genuine actual deformation として bundle する -/

/--
一つの保持境界を消す canonical step の actual 幾何データ。

`pattern_step` は P32 の Boolean 削除、`replacement` は同じ step の fixed-fiber 実現、
`ferrers_down` と `point_ne` は P33 により strict downward であることを記録する。
-/
structure ActualCanonicalBoundaryDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) : Prop where
  pattern_step : CanonicalBoundaryDeletion D R S
  replacement :
    BlockReplacement
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (canonicalFlatPoint P hPrimitive hReduced u D S)
      1 P.oddCount
  source_firstCrossing :
    FirstCrossing
      (canonicalFlatPoint P hPrimitive hReduced u D R).word
  target_firstCrossing :
    FirstCrossing
      (canonicalFlatPoint P hPrimitive hReduced u D S).word
  ferrers_down :
    FiberPoint.FerrersLe
      (canonicalFlatPoint P hPrimitive hReduced u D S)
      (canonicalFlatPoint P hPrimitive hReduced u D R)
  point_ne :
    canonicalFlatPoint P hPrimitive hReduced u D S ≠
      canonicalFlatPoint P hPrimitive hReduced u D R

/--
P32 の一境界削除は必ず `ActualCanonicalBoundaryDeletion` として実現される。
-/
theorem actualCanonicalBoundaryDeletion_of_pattern
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hDel : CanonicalBoundaryDeletion D R S) :
    ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S := by
  have hStrict :=
    canonicalFlatPoint_strict_of_retained_lt
      P hPrimitive hReduced u D
      (R := S) (S := R) hDel.le hDel.ne
  refine {
    pattern_step := hDel
    replacement := canonicalFlatPoint_blockReplacement_one_terminal
      P hPrimitive hReduced u D R S
    source_firstCrossing := ?_
    target_firstCrossing := ?_
    ferrers_down := hStrict.1
    point_ne := hStrict.2
  }
  · unfold canonicalFlatPoint
    exact canonicalFlatRepresentative_firstCrossing
      P hPrimitive hReduced u D R
  · unfold canonicalFlatPoint
    exact canonicalFlatRepresentative_firstCrossing
      P hPrimitive hReduced u D S

/-- actual 一境界削除は Boolean 順序でも下向き。 -/
theorem ActualCanonicalBoundaryDeletion.pattern_le
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (A : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S) :
    S.Le R :=
  A.pattern_step.le

/-- actual 一境界削除は target と source を同一視しない。 -/
theorem ActualCanonicalBoundaryDeletion.pattern_ne
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (A : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S) :
    S ≠ R :=
  A.pattern_step.ne

/-!
## 主定理

canonical boundary deletion は、標準平坦 FirstCrossing family 内の
strict downward actual Ferrers deformation そのものである。
-/
theorem canonicalBoundaryDeletion_iff_actual
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    CanonicalBoundaryDeletion D R S ↔
      ActualCanonicalBoundaryDeletion
        P hPrimitive hReduced u D R S := by
  constructor
  · exact actualCanonicalBoundaryDeletion_of_pattern
      P hPrimitive hReduced u D
  · intro A
    exact A.pattern_step

end RecordFerrers
end Collatz2
