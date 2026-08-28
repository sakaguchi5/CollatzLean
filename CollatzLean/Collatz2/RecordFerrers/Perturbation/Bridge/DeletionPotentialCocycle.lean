import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationCanonicity

/-!
# Record–Ferrers Perturbation / Deletion Potential Cocycle

`ArithmeticDecorationCanonicity` までで、actual source は canonical に

  actual source
      |
      | decorationGap
      v
  canonical flat top
      |
      v
  canonical flat Boolean family
      |
      v
  absolute bottom

へ射影され、上段の `canonicalFlatTop` と `decorationGap` は
RecordDecomposition の選択に依存しないことが分かった。

一方 P34--P35 では、canonical flat Boolean family 上の一境界削除が
actual fixed-fiber deformation として実現され、有限・停止・合流し、
Boolean inclusion と actual reachability が exact に一致することまで閉じている。

本ファイルでは、その削除系へ genuine `affineConst` の算術量を載せる。

中心量は

  deletionCost R S = flatAffine R - flatAffine S

である。`S.Le R` の下では flat affine potential は単調なので、この差は
actual arithmetic loss を表す。

さらに `T.Le S.Le R` なら

  deletionCost R T
    = deletionCost R S + deletionCost S T

が exact に成り立つ。従って deletion cost は Boolean deletion category 上の
additive cocycle / conservative potential difference である。

削除経路については、Prop から Nat への非自明な elimination を避けるため、
`ActualDeletionTraceCost R S c` という Prop-valued relation を導入する。
任意の trace cost `c` が endpoint difference `deletionCost R S` と一致することを示し、
同じ endpoints を持つ二経路の総 cost が必ず等しいことを得る。

特に canonical flat top から absolute bottom までの任意の actual deletion trace は

  total cost = boundaryGap

を満たす。これが本ファイルの主定理である。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. canonical flat family 上の affine potential -/

/-- Boolean pattern に対応する canonical flat point の genuine `affineConst`。 -/
def flatAffine
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : ℕ :=
  affineConst (canonicalFlatPoint P hPrimitive hReduced u D R).word

/-- Boolean inclusion を下向きに進むと flat affine potential は増加しない。 -/
theorem flatAffine_mono_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    flatAffine P hPrimitive hReduced u D S ≤
      flatAffine P hPrimitive hReduced u D R := by
  have hFerrers :
      FiberPoint.FerrersLe
        (canonicalFlatPoint P hPrimitive hReduced u D S)
        (canonicalFlatPoint P hPrimitive hReduced u D R) :=
    canonicalFlatPoint_ferrersLe_of_retainedLe
      P hPrimitive hReduced u D hSR
  unfold flatAffine
  rw [affineConst_eq_base_add_weightedArea,
      affineConst_eq_base_add_weightedArea]
  exact Nat.add_le_add_left (weightedArea_mono hFerrers) _

/-! ## 2. deletion cost と additive cocycle law -/

/--
`R` から下側の `S` へ進むときに失われる genuine affine arithmetic。
順序仮定なしでも Nat subtraction として定義し、主要定理では `S.Le R` を仮定する。
-/
def deletionCost
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) : ℕ :=
  flatAffine P hPrimitive hReduced u D R -
    flatAffine P hPrimitive hReduced u D S

@[simp] theorem deletionCost_self
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    deletionCost P hPrimitive hReduced u D R R = 0 := by
  simp [deletionCost]

/--
## Cocycle law

`T ≤ S ≤ R` なら endpoint difference は途中点 `S` で exact に加法分解する。
これが deletion arithmetic の基本保存則。
-/
theorem deletionCost_add_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S T : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (hTS : T.Le S) :
    deletionCost P hPrimitive hReduced u D R T =
      deletionCost P hPrimitive hReduced u D R S +
        deletionCost P hPrimitive hReduced u D S T := by
  have hSleR :=
    flatAffine_mono_of_retainedLe
      P hPrimitive hReduced u D hSR
  have hTleS :=
    flatAffine_mono_of_retainedLe
      P hPrimitive hReduced u D hTS
  have hTleR :
      flatAffine P hPrimitive hReduced u D T ≤
        flatAffine P hPrimitive hReduced u D R :=
    hTleS.trans hSleR
  unfold deletionCost
  omega

/-- actual 一境界削除の arithmetic cost は strict positive。 -/
theorem deletionCost_pos_of_actualCanonicalBoundaryDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (A : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S) :
    0 < deletionCost P hPrimitive hReduced u D R S := by
  have hLt := A.affineConst_lt P hPrimitive hReduced u D
  unfold deletionCost flatAffine
  omega

/--
下向き Boolean comparable な二点では deletion cost が 0 であることと
pattern equality が exact に同値。
-/
theorem deletionCost_eq_zero_iff_eq_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    deletionCost P hPrimitive hReduced u D R S = 0 ↔ R = S := by
  constructor
  · intro hCost
    have hLe :=
      flatAffine_mono_of_retainedLe
        P hPrimitive hReduced u D hSR
    have hAffine :
        flatAffine P hPrimitive hReduced u D R =
          flatAffine P hPrimitive hReduced u D S := by
      unfold deletionCost at hCost
      omega
    have hPoint :
        canonicalFlatPoint P hPrimitive hReduced u D R =
          canonicalFlatPoint P hPrimitive hReduced u D S := by
      apply fiberPoint_eq_of_same_affineConst
      simpa [flatAffine] using hAffine
    exact canonicalFlatPoint_injective
      P hPrimitive hReduced u D hPoint
  · intro hEq
    subst S
    exact deletionCost_self P hPrimitive hReduced u D R

/-- strict Boolean descent は positive arithmetic loss を持つ。 -/
theorem deletionCost_pos_of_retained_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (hne : S ≠ R) :
    0 < deletionCost P hPrimitive hReduced u D R S := by
  have hNonzero :
      deletionCost P hPrimitive hReduced u D R S ≠ 0 := by
    intro hZero
    have hEq :=
      (deletionCost_eq_zero_iff_eq_of_retainedLe
        P hPrimitive hReduced u D hSR).1 hZero
    exact hne hEq.symm
  exact Nat.pos_of_ne_zero hNonzero

/-! ## 3. top-relative boundary potential -/

/--
canonical flat top から pattern `R` までに累積した arithmetic boundary loss。
これは top から `R` への deletion cost そのもの。
-/
def boundaryPotential
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : ℕ :=
  deletionCost P hPrimitive hReduced u D
    (retainAllBoundaries D) R

@[simp] theorem boundaryPotential_top
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryPotential P hPrimitive hReduced u D
      (retainAllBoundaries D) = 0 := by
  simp [boundaryPotential]

/--
`R` から `S` へ下向きに進むと、top-relative potential は
その deletion cost だけ exact に増える。
-/
theorem boundaryPotential_step
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    boundaryPotential P hPrimitive hReduced u D S =
      boundaryPotential P hPrimitive hReduced u D R +
        deletionCost P hPrimitive hReduced u D R S := by
  unfold boundaryPotential
  exact deletionCost_add_of_retainedLe
    P hPrimitive hReduced u D
    (RetainedBoundaryPattern.le_all D R) hSR

/-- absolute bottom での accumulated boundary potential は Bridge の `boundaryGap`。 -/
theorem boundaryPotential_bottom_eq_boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryPotential P hPrimitive hReduced u D
        (retainNoBoundaries D) =
      boundaryGap P hPrimitive hReduced u D := by
  rfl

/-- top から bottom への endpoint deletion cost は exact に `boundaryGap`。 -/
theorem deletionCost_top_bottom_eq_boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    deletionCost P hPrimitive hReduced u D
        (retainAllBoundaries D) (retainNoBoundaries D) =
      boundaryGap P hPrimitive hReduced u D := by
  exact boundaryPotential_bottom_eq_boundaryGap
    P hPrimitive hReduced u D

/-! ## 4. cost を持つ actual deletion trace -/

/--
actual canonical deletion の有限列と、その各 edge cost の総和を同時に記録する relation。

Prop-valued にすることで proof object から Nat を直接取り出す必要をなくす。
-/
inductive ActualDeletionTraceCost
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    RetainedBoundaryPattern D → RetainedBoundaryPattern D → ℕ → Prop
  | refl (R : RetainedBoundaryPattern D) :
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R R 0
  | tail
      {R S T : RetainedBoundaryPattern D}
      {c : ℕ} :
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R S c →
      ActualCanonicalBoundaryDeletion
        P hPrimitive hReduced u D S T →
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R T
        (c + deletionCost P hPrimitive hReduced u D S T)

namespace ActualDeletionTraceCost

/-- cost trace は既存 P35 の actual reachability を忘却して持つ。 -/
theorem reachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D R S c) :
    ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R S := by
  induction T with
  | refl =>
      exact ActualCanonicalDeletionReachable.refl R
  | tail hTrace A ih =>
      exact ActualCanonicalDeletionReachable.tail ih A

/--
## Endpoint exactness

任意の actual deletion trace の総 cost は、その endpoints の affine potential difference
`deletionCost R S` に exact に一致する。
-/
theorem eq_endpoint_deletionCost
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D R S c) :
    c = deletionCost P hPrimitive hReduced u D R S := by
  induction T with
  | refl =>
      simp [deletionCost]
  | @tail S T c hTrace A ih =>
      have hReach :
          ActualCanonicalDeletionReachable
            P hPrimitive hReduced u D R S :=
        reachable P hPrimitive hReduced u D hTrace
      have hSR : S.Le R :=
        ActualCanonicalDeletionReachable.pattern_le
          P hPrimitive hReduced u D hReach
      have hTS : T.Le S := A.pattern_step.le
      rw [ih]
      exact
        (deletionCost_add_of_retainedLe
          P hPrimitive hReduced u D hSR hTS).symm

/-- 同じ endpoints を持つ actual deletion trace の総 cost は一意。 -/
theorem path_independent
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    {c d : ℕ}
    (Tc : ActualDeletionTraceCost
      P hPrimitive hReduced u D R S c)
    (Td : ActualDeletionTraceCost
      P hPrimitive hReduced u D R S d) :
    c = d := by
  calc
    c = deletionCost P hPrimitive hReduced u D R S :=
      eq_endpoint_deletionCost P hPrimitive hReduced u D Tc
    _ = d :=
      (eq_endpoint_deletionCost P hPrimitive hReduced u D Td).symm

end ActualDeletionTraceCost

/-! ## 5. P35 reachability と cost trace の exact 接続 -/

/-- P35 の任意の reachable pair には、その経路に対応する cost trace が存在する。 -/
theorem exists_actualDeletionTraceCost_of_reachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hReach : ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R S) :
    ∃ c : ℕ,
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R S c := by
  induction hReach with
  | refl =>
      exact ⟨0, ActualDeletionTraceCost.refl R⟩
  | @tail S T hRS A ih =>
      rcases ih with ⟨c, hCost⟩
      exact ⟨
        c + deletionCost P hPrimitive hReduced u D S T,
        ActualDeletionTraceCost.tail hCost A
      ⟩

/-- Boolean inclusion `S.Le R` なら endpoint-determined cost trace が存在する。 -/
theorem exists_actualDeletionTraceCost_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    ∃ c : ℕ,
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R S c := by
  exact exists_actualDeletionTraceCost_of_reachable
    P hPrimitive hReduced u D
    (actualReachable_of_retainedLe
      P hPrimitive hReduced u D hSR)

/-- 任意 pattern から absolute bottom への cost trace が存在する。 -/
theorem exists_actualDeletionTraceCost_to_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ∃ c : ℕ,
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R (retainNoBoundaries D) c := by
  exact exists_actualDeletionTraceCost_of_reachable
    P hPrimitive hReduced u D
    (actualReachable_to_none P hPrimitive hReduced u D R)

/-! ## 6. 主定理: top-to-bottom arithmetic path independence -/

/--
任意の canonical top-to-bottom actual deletion trace の総 arithmetic cost は
Bridge の canonical `boundaryGap` に exact に一致する。

従って削除順序は arithmetic total loss に影響しない。
-/
theorem actualDeletionTraceCost_top_bottom_eq_boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D) c) :
    c = boundaryGap P hPrimitive hReduced u D := by
  calc
    c = deletionCost P hPrimitive hReduced u D
        (retainAllBoundaries D) (retainNoBoundaries D) :=
      ActualDeletionTraceCost.eq_endpoint_deletionCost
        P hPrimitive hReduced u D T
    _ = boundaryGap P hPrimitive hReduced u D :=
      deletionCost_top_bottom_eq_boundaryGap
        P hPrimitive hReduced u D

/-- top-to-bottom trace は存在し、その総 cost は `boundaryGap` に一意に固定される。 -/
theorem exists_top_bottom_trace_with_boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D)
      (boundaryGap P hPrimitive hReduced u D) := by
  rcases exists_actualDeletionTraceCost_to_bottom
      P hPrimitive hReduced u D (retainAllBoundaries D) with
    ⟨c, hTrace⟩
  have hEq :=
    actualDeletionTraceCost_top_bottom_eq_boundaryGap
      P hPrimitive hReduced u D hTrace
  simpa [hEq] using hTrace

/--
同じ top-to-bottom endpoints を持つ任意の二 actual deletion trace は、
削除順序が異なっても同じ `boundaryGap` を総 cost として持つ。
-/
theorem top_bottom_arithmetic_path_independent
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c d : ℕ}
    (Tc : ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D) c)
    (Td : ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D) d) :
    c = d ∧
      c = boundaryGap P hPrimitive hReduced u D ∧
      d = boundaryGap P hPrimitive hReduced u D := by
  have hc :=
    actualDeletionTraceCost_top_bottom_eq_boundaryGap
      P hPrimitive hReduced u D Tc
  have hd :=
    actualDeletionTraceCost_top_bottom_eq_boundaryGap
      P hPrimitive hReduced u D Td
  exact ⟨hc.trans hd.symm, hc, hd⟩

/-! ## 7. Bridge 三層分解との統合 -/

/--
actual arithmetic は

  absolute base
  + 任意 top-to-bottom deletion trace の総 cost
  + canonical decorationGap

へ exact に分解する。

trace cost は上の主定理により削除経路に依存しない。
-/
theorem affineConst_eq_absoluteBase_add_traceCost_add_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D) c) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) + c +
        decorationGap P hPrimitive hReduced u D := by
  have hCost :=
    actualDeletionTraceCost_top_bottom_eq_boundaryGap
      P hPrimitive hReduced u D T
  rw [hCost]
  exact affineConst_eq_canonical_three_layer_decomposition
    P hPrimitive hReduced u D

/-! ## 8. closure package -/

/--
canonical deletion system に載る arithmetic cocycle の閉包データ。

* Boolean descent に沿う potential monotonicity
* endpoint cost の additive cocycle law
* actual edge の strict positivity
* top potential = 0
* bottom potential = boundaryGap
* trace cost の endpoint exactness

を一つにまとめる。
-/
structure CanonicalDeletionPotentialCocycleClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  flat_mono :
    ∀ {R S : RetainedBoundaryPattern D},
      S.Le R →
      flatAffine P hPrimitive hReduced u D S ≤
        flatAffine P hPrimitive hReduced u D R
  cocycle :
    ∀ {R S T : RetainedBoundaryPattern D},
      S.Le R → T.Le S →
      deletionCost P hPrimitive hReduced u D R T =
        deletionCost P hPrimitive hReduced u D R S +
          deletionCost P hPrimitive hReduced u D S T
  edge_positive :
    ∀ {R S : RetainedBoundaryPattern D},
      ActualCanonicalBoundaryDeletion
        P hPrimitive hReduced u D R S →
      0 < deletionCost P hPrimitive hReduced u D R S
  top_zero :
    boundaryPotential P hPrimitive hReduced u D
      (retainAllBoundaries D) = 0
  bottom_exact :
    boundaryPotential P hPrimitive hReduced u D
        (retainNoBoundaries D) =
      boundaryGap P hPrimitive hReduced u D
  trace_exact :
    ∀ {R S : RetainedBoundaryPattern D} {c : ℕ},
      ActualDeletionTraceCost
          P hPrimitive hReduced u D R S c →
        c = deletionCost P hPrimitive hReduced u D R S

/--
## Record--Ferrers deletion potential cocycle closure theorem

P34--P35 の finite confluent deletion geometry は genuine affine arithmetic を
path-independent additive cocycle として運ぶ。
-/
theorem canonicalDeletionPotentialCocycle_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    CanonicalDeletionPotentialCocycleClosed
      P hPrimitive hReduced u D := by
  refine {
    flat_mono := ?_
    cocycle := ?_
    edge_positive := ?_
    top_zero := boundaryPotential_top
      P hPrimitive hReduced u D
    bottom_exact := boundaryPotential_bottom_eq_boundaryGap
      P hPrimitive hReduced u D
    trace_exact := ?_
  }
  · intro R S hSR
    exact flatAffine_mono_of_retainedLe
      P hPrimitive hReduced u D hSR
  · intro R S T hSR hTS
    exact deletionCost_add_of_retainedLe
      P hPrimitive hReduced u D hSR hTS
  · intro R S A
    exact deletionCost_pos_of_actualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D A
  · intro R S c T
    exact ActualDeletionTraceCost.eq_endpoint_deletionCost
      P hPrimitive hReduced u D T

end RecordFerrers
end Collatz2
