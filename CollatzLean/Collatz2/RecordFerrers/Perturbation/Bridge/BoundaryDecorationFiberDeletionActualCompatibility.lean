import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationCanonicalMergeCompactSupport

/-!
# Record–Ferrers Perturbation / Fiber Deletion Actual Compatibility

`ProductDecorationDeletionSystem` では fixed skeleton 上の decoration dynamics を

  LocalDecorationTupleCellDeletion

の asynchronous product として定義し、それを

  FixedSkeletonProductCellDeletion

として actual fixed-skeleton state space へ transport した。
一方 `LocalDecorationDeletionSystem` / `ProperLocalDecorationSupport` では、actual Ferrers geometry
上の genuine one-cell deletion と、その一つの RecordBlock 内への compact-support localization
を構成した。

本ファイルはこの二つを接続する。

中心となる事実は、genuine RecordBlock `B : RecordBlock x a r` の内部では

  global excess(a+j)
    = criticalExcess(a) + local excess(j)

となることである。RecordBlock start は critical roof に固定されるので、fixed skeleton の
whole Ferrers profile は各 local Ferrers profile を skeleton だけで決まる baseline だけ縦に
平行移動して並べたものと読める。

従って一つの local factor の Ferrers one-cell deletion は、whole fixed-skeleton Ferrers profile
でも exact に一つの column だけを一セル下げる。

本ファイルでは

* product tuple step が具体的に一つの local block replacement であること
* local one-cell cover を whole fixed-chord one-cell cover へ持ち上げる splice lemma
* `FixedSkeletonProductCellDeletion` から actual `FerrersShape.IsUnitCover` への compatibility
* arbitrary fixed-skeleton actual one-cell cover の genuine common RecordBlock support
* 各 `BoundaryDecorationActualFiber` / abstract boundary fiber への specialization

を閉じる。

ここで actual relation は元 top decomposition の decoration interval に依存しない
`FixedSkeletonActualCellDeletion` として定義する。これにより任意の coarse boundary fiber 上で
同じ compatibility theorem を使用できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. product one-cell step は一つの concrete local block replacement -/

/--
product tuple one-cell step の concrete block-list split。

source / target は同じ prefix / suffix を持ち、exact に一つの local decoration
`A -> B` だけが変化する。
-/
structure LocalDecorationTupleCellDeletionSplit
    {rs : List ℕ}
    (S T : LocalDecorationTuple rs) where
  r : ℕ
  A : LocalDecoration r
  B : LocalDecoration r
  pre : List Word
  post : List Word
  source_blocks : S.blocks = pre ++ (A.word :: post)
  target_blocks : T.blocks = pre ++ (B.word :: post)
  local_step : LocalDecorationCellDeletion A B

namespace LocalDecorationTupleCellDeletion

/--
product tuple one-cell step は concrete block list 上で
exact に一箇所だけ変化する split を持つ。
-/
private theorem exists_split_nonempty
    {rs : List ℕ}
    {S T : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion S T) :
    Nonempty (LocalDecorationTupleCellDeletionSplit S T) := by
  induction h with
  | @head r rs A B T hAB =>
      exact ⟨{
        r := r
        A := A
        B := B
        pre := []
        post := T.blocks
        source_blocks := by
          simp
        target_blocks := by
          simp
        local_step := hAB
      }⟩
  | @tail r rs A T U hTU ih =>
      rcases ih with ⟨W⟩
      exact ⟨{
        r := W.r
        A := W.A
        B := W.B
        pre := A.word :: W.pre
        post := W.post
        source_blocks := by
          simp only [LocalDecorationTuple.blocks_cons]
          rw [W.source_blocks]
          simp only [List.cons_append]
        target_blocks := by
          simp only [LocalDecorationTuple.blocks_cons]
          rw [W.target_blocks]
          simp only [List.cons_append]
        local_step := W.local_step
      }⟩


/--
product tuple one-cell step から、
concrete block list 上の exact な一箇所の変化を取り出す。
-/
noncomputable def exists_split
    {rs : List ℕ}
    {S T : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion S T) :
    LocalDecorationTupleCellDeletionSplit S T :=
  Classical.choice (exists_split_nonempty h)

end LocalDecorationTupleCellDeletion

/-- local one-cell step の source / target は同じ length を持つ。 -/
theorem LocalDecorationCellDeletion.word_length_eq
    {r : ℕ}
    {A B : LocalDecoration r}
    (_h : LocalDecorationCellDeletion A B) :
    A.word.length = B.word.length := by
  simpa [oddSteps] using A.length_eq.trans B.length_eq.symm

/-- local one-cell step の source / target は同じ total two-depth を持つ。 -/
theorem LocalDecorationCellDeletion.twoSteps_eq
    {r : ℕ}
    {A B : LocalDecoration r}
    (_h : LocalDecorationCellDeletion A B) :
    twoSteps A.word = twoSteps B.word := by
  have hA := A.validMinimal.toMinimalBlock.minimalDepth
  have hB := B.validMinimal.toMinimalBlock.minimalDepth
  rw [A.length_eq] at hA
  rw [B.length_eq] at hB
  omega

/-! ## 2. fixed-skeleton assembly の whole-word exactness -/

/-- tuple から fixed-skeleton source へ戻した point の word は explicit assembly word そのもの。 -/
@[simp] theorem fixedSkeletonSourceOfTuple_word
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    (fixedSkeletonSourceOfTuple
      P hPrimitive hReduced u D T).1.word =
      fixedSkeletonAnchor u ++ T.blocks.flatten := by
  rfl

/-- 任意 fixed-skeleton source の whole word は extracted local blocks の explicit concatenation。 -/
theorem FixedSkeletonSource.word_eq_anchor_append_blocks
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    X.1.word =
      fixedSkeletonAnchor u ++ X.toLocalDecorationTuple.blocks.flatten := by
  have hRound :=
    fixedSkeletonSource_roundtrip
      P hPrimitive hReduced u D X
  have hWord := congrArg (fun Z => Z.1.word) hRound
  simpa only [fixedSkeletonSourceOfTuple_word] using hWord.symm

/-! ## 2. local RecordBlock profile と global Ferrers profile の exact bridge -/

/--
RecordBlock start が roof 上にあるため、block 内の global excess は
`criticalExcess start + local excess` に exact 分解する。
-/
theorem RecordBlock.globalExcess_eq_criticalExcess_add_localExcess
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len j : ℕ}
    (B : RecordBlock x start len)
    (hj : j ≤ len) :
    x.excessAt (start + j) =
      criticalExcess start +
        (LocalDecoration.toFiberPoint {
          word := blockWord x start len
          validMinimal := {
            toMinimalBlock := B.minimal
            valid := RecordBlock.local_valid
          }
          length_eq := B.local_oddSteps
        }).excessAt j := by
  let L : LocalDecoration len := {
    word := blockWord x start len
    validMinimal := {
      toMinimalBlock := B.minimal
      valid := RecordBlock.local_valid
    }
    length_eq := B.local_oddSteps
  }
  have hStartRoof := B.start_roof
  change x.height start = criticalHeight start at hStartRoof
  have hAdd := FiberPoint.prefixTwoDepth_add_drop x.word start j
  have hSlice :=
    prefixTwoDepth_blockWord x start len j hj
  change
    prefixTwoDepth x.word (start + j) =
      prefixTwoDepth x.word start +
        prefixTwoDepth (x.word.drop start) j
    at hAdd
  rw [← hSlice] at hAdd
  have hLocal :=
    L.toFiberPoint.height_eq_index_add_excess hj
  change
    prefixTwoDepth (blockWord x start len) j =
      j + L.toFiberPoint.excessAt j
    at hLocal
  /-
  global height は、block 開始時の height に
  block 内の local height を加えたものになる。
  -/
  have hHeightAdd :
      x.height (start + j) =
        x.height start +
          (j + L.toFiberPoint.excessAt j) := by
    calc
      x.height (start + j)
          =
        x.height start +
          prefixTwoDepth (blockWord x start len) j := by
            exact hAdd
      _ =
        x.height start +
          (j + L.toFiberPoint.excessAt j) := by
            rw [hLocal]
  /-
  RecordBlock の開始点は critical roof 上にあるので、
  global height の開始値を criticalHeight に置き換える。
  -/
  have hHeightCritical :
      x.height (start + j) =
        criticalHeight start +
          (j + L.toFiberPoint.excessAt j) := by
    calc
      x.height (start + j)
          =
        x.height start +
          (j + L.toFiberPoint.excessAt j) :=
            hHeightAdd
      _ =
        criticalHeight start +
          (j + L.toFiberPoint.excessAt j) := by
            rw [hStartRoof]
  /-
  criticalHeight は少なくとも index start 以上。
  これを明示して Nat.sub の切り捨てを排除する。
  -/
  have hCriticalLe :
      start ≤ criticalHeight start := by
    exact index_le_criticalHeight start
  unfold criticalExcess
  change
    x.height (start + j) - (start + j) =
      (criticalHeight start - start) +
        L.toFiberPoint.excessAt j
  omega

/--
同じ位置・長さの genuine RecordBlock では、global column comparison は local column comparison と同値。
-/
theorem RecordBlock.globalColumn_eq_iff_localColumn_eq
    {p H : ℕ}
    {x y : FiberPoint p H}
    {start len j : ℕ}
    (Bx : RecordBlock x start len)
    (By : RecordBlock y start len)
    (hj : j < len)
    (hGlobal : start + j < p) :
    x.toFerrersShape.column ⟨start + j, hGlobal⟩ =
        y.toFerrersShape.column ⟨start + j, hGlobal⟩ ↔
      (LocalDecoration.ferrersShape {
        word := blockWord x start len
        validMinimal := {
          toMinimalBlock := Bx.minimal
          valid := RecordBlock.local_valid
        }
        length_eq := Bx.local_oddSteps
      }).column ⟨j, hj⟩ =
      (LocalDecoration.ferrersShape {
        word := blockWord y start len
        validMinimal := {
          toMinimalBlock := By.minimal
          valid := RecordBlock.local_valid
        }
        length_eq := By.local_oddSteps
      }).column ⟨j, hj⟩ := by
  let Ax : LocalDecoration len := {
    word := blockWord x start len
    validMinimal := {
      toMinimalBlock := Bx.minimal
      valid := RecordBlock.local_valid
    }
    length_eq := Bx.local_oddSteps
  }
  let Ay : LocalDecoration len := {
    word := blockWord y start len
    validMinimal := {
      toMinimalBlock := By.minimal
      valid := RecordBlock.local_valid
    }
    length_eq := By.local_oddSteps
  }
  have hx := Bx.globalExcess_eq_criticalExcess_add_localExcess (Nat.le_of_lt hj)
  have hy := By.globalExcess_eq_criticalExcess_add_localExcess (Nat.le_of_lt hj)
  change
    x.excessAt (start + j) = y.excessAt (start + j) ↔
      Ax.toFiberPoint.excessAt j = Ay.toFiberPoint.excessAt j
  rw [hx, hy]
  simp only [Nat.add_left_cancel_iff, Ax, Ay]

/-! ## 3. explicit word splice の prefix-depth lemmas -/

/-- common prefix の内部では middle block の選択は prefix depth に影響しない。 -/
theorem prefixTwoDepth_splice_eq_of_before
    (pre A B post : Word)
    {k : ℕ}
    (hk : k ≤ pre.length) :
    prefixTwoDepth (pre ++ A ++ post) k =
      prefixTwoDepth (pre ++ B ++ post) k := by
  unfold prefixTwoDepth
  simp [List.take_append, hk]

/--
common prefix の直後、middle block 内の cut は
`twoSteps pre + middle prefix depth` に exact 分解する。
-/
theorem prefixTwoDepth_splice_middle
    (pre mid post : Word)
    {j : ℕ}
    (hj : j ≤ mid.length) :
    prefixTwoDepth (pre ++ mid ++ post) (pre.length + j) =
      twoSteps pre + prefixTwoDepth mid j := by
  unfold prefixTwoDepth
  simp only [List.append_assoc, List.take_append, add_tsub_cancel_left, hj,
              Nat.sub_eq_zero_of_le, List.take_zero,
              List.append_nil, twoSteps_append, Nat.add_right_cancel_iff]
  rw [List.take_of_length_le]
  omega


/-- middle blocks の length / total depth が同じなら、その完全な右側の prefix depth は同じ。 -/
theorem prefixTwoDepth_splice_eq_of_after
    (pre A B post : Word)
    (hLen : A.length = B.length)
    (hTwo : twoSteps A = twoSteps B)
    {k : ℕ}
    (hk : pre.length + A.length ≤ k) :
    prefixTwoDepth (pre ++ A ++ post) k =
      prefixTwoDepth (pre ++ B ++ post) k := by
  let t := k - (pre.length + A.length)
  have hkA : k = pre.length + A.length + t := by
    dsimp [t]
    omega
  rw [hkA]
  unfold prefixTwoDepth
  simp only [hLen, Nat.add_assoc, List.append_assoc, List.take_append,
              add_tsub_cancel_left, twoSteps_append,
              Nat.add_left_cancel_iff, Nat.add_right_cancel_iff]
  have hTakeA :
      A.length ≤ B.length + t := by
    omega
  have hTakeB :
      B.length ≤ B.length + t := by
    omega
  rw [
    List.take_of_length_le hTakeA,
    List.take_of_length_le hTakeB
  ]
  exact hTwo

/-! ## 4. Ferrers shape の一列 lowering から unit cover を回収 -/

/--
exact に一列だけ 1 小さい Ferrers profile は ordinary area も exact に 1 小さい。
-/
theorem FerrersShape.area_succ_of_unique_lowering
    {p : ℕ}
    {A B : FerrersShape p}
    (i : Fin p)
    (hi : A.column i + 1 = B.column i)
    (hOther : ∀ j : Fin p, j ≠ i → A.column j = B.column j) :
    FerrersShape.area B = FerrersShape.area A + 1 := by
  unfold FerrersShape.area
  have hiMem : i.1 ∈ Finset.range p := Finset.mem_range.mpr i.isLt
  calc
    Finset.sum (Finset.range p) (fun k => B.atNat k)
        = Finset.sum (Finset.range p) (fun k =>
            A.atNat k + if k = i.1 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkLt : k < p := Finset.mem_range.mp hk
          by_cases hki : k = i.1
          · subst k
            simp [FerrersShape.atNat, i.isLt, hi]
          · have hFin : (⟨k, hkLt⟩ : Fin p) ≠ i := by
              intro hEq
              exact hki (congrArg Fin.val hEq)
            have hEq := hOther ⟨k, hkLt⟩ hFin
            simpa [FerrersShape.atNat, hkLt, hki] using hEq.symm
    _ = Finset.sum (Finset.range p) (fun k => A.atNat k) +
          Finset.sum (Finset.range p) (fun k => if k = i.1 then 1 else 0) := by
        rw [Finset.sum_add_distrib]
    _ = Finset.sum (Finset.range p) (fun k => A.atNat k) + 1 := by
        simp [hiMem]

/-- exact に一列だけ 1 小さい Ferrers profile は unit cover。 -/
theorem FerrersShape.isUnitCover_of_unique_lowering
    {p : ℕ}
    {A B : FerrersShape p}
    (i : Fin p)
    (hi : A.column i + 1 = B.column i)
    (hOther : ∀ j : Fin p, j ≠ i → A.column j = B.column j) :
    FerrersShape.IsUnitCover A B := by
  have hLe : A.Le B := by
    intro j
    by_cases hji : j = i
    · subst j
      omega
    · rw [hOther j hji]
  have hArea := FerrersShape.area_succ_of_unique_lowering i hi hOther
  exact FerrersShape.isUnitCover_of_le_area_succ hLe hArea

/-! ## 5. local one-cell splice は whole fixed-chord one-cell splice -/

/--
同じ global index で height が等しければ excess も等しい。
`height = index + excess` の共通 index を消去するだけ。
-/
private theorem fiberPoint_excessAt_eq_of_height_eq
    {p H : ℕ}
    {x y : FiberPoint p H}
    {k : ℕ}
    (hk : k ≤ p)
    (hHeight : x.height k = y.height k) :
    x.excessAt k = y.excessAt k := by
  have hx :=
    x.height_eq_index_add_excess hk
  have hy :=
    y.height_eq_index_add_excess hk
  omega


/--
同じ global index で target height が source height より exact に 1 小さければ、
excess も exact に 1 小さい。
-/
private theorem fiberPoint_excessAt_add_one_eq_of_height_add_one_eq
    {p H : ℕ}
    {x y : FiberPoint p H}
    {k : ℕ}
    (hk : k ≤ p)
    (hHeight : y.height k + 1 = x.height k) :
    y.excessAt k + 1 = x.excessAt k := by
  have hx :=
    x.height_eq_index_add_excess hk
  have hy :=
    y.height_eq_index_add_excess hk
  omega


/--
同じ local index で excess が等しければ prefix depth も等しい。
-/
private theorem localDecoration_prefixTwoDepth_eq_of_excessAt_eq
    {r : ℕ}
    (A B : LocalDecoration r)
    {j : ℕ}
    (hj : j ≤ r)
    (hEx :
      A.toFiberPoint.excessAt j =
        B.toFiberPoint.excessAt j) :
    prefixTwoDepth A.word j =
      prefixTwoDepth B.word j := by
  have hA :=
    A.toFiberPoint.height_eq_index_add_excess hj
  have hB :=
    B.toFiberPoint.height_eq_index_add_excess hj
  change
    prefixTwoDepth A.word j =
      j + A.toFiberPoint.excessAt j
    at hA
  change
    prefixTwoDepth B.word j =
      j + B.toFiberPoint.excessAt j
    at hB
  omega


/--
同じ local index で B の excess が A より exact に 1 小さければ、
prefix depth も exact に 1 小さい。
-/
private theorem localDecoration_prefixTwoDepth_add_one_eq_of_excessAt_add_one_eq
    {r : ℕ}
    (A B : LocalDecoration r)
    {j : ℕ}
    (hj : j ≤ r)
    (hEx :
      B.toFiberPoint.excessAt j + 1 =
        A.toFiberPoint.excessAt j) :
    prefixTwoDepth B.word j + 1 =
      prefixTwoDepth A.word j := by
  have hA :=
    A.toFiberPoint.height_eq_index_add_excess hj
  have hB :=
    B.toFiberPoint.height_eq_index_add_excess hj
  change
    prefixTwoDepth A.word j =
      j + A.toFiberPoint.excessAt j
    at hA
  change
    prefixTwoDepth B.word j =
      j + B.toFiberPoint.excessAt j
    at hB
  omega

/--
同じ prefix / suffix の間で一つの local minimal blockだけを one-cell downward に変えると、
whole fixed-chord Ferrers profile も exact one-cell downward になる。
-/
theorem FiberPoint.isUnitCover_of_localDecorationSplice
    {p H r : ℕ}
    (x y : FiberPoint p H)
    (pre post : Word)
    (A B : LocalDecoration r)
    (hx : x.word = pre ++ A.word ++ post)
    (hy : y.word = pre ++ B.word ++ post)
    (hLocal : LocalDecorationCellDeletion A B) :
    FerrersShape.IsUnitCover y.toFerrersShape x.toFerrersShape := by
  rcases hLocal.exists_unique_changed_column with
    ⟨j, hjExact, hjOnly⟩
  have hALen : A.word.length = r := by
    simpa [oddSteps] using A.length_eq
  have hBLen : B.word.length = r := by
    simpa [oddSteps] using B.length_eq
  have hTwo :
      twoSteps A.word = twoSteps B.word :=
    hLocal.twoSteps_eq
  have hxLen : x.word.length = p := by
    simpa [oddSteps] using x.oddSteps_eq
  have hFactorLen :
      pre.length + r + post.length = p := by
    rw [hx] at hxLen
    simp [hALen] at hxLen
    omega
  let kVal : ℕ := pre.length + j.1
  have hkLt : kVal < p := by
    dsimp [kVal]
    have hjLt : j.1 < r := j.isLt
    omega
  have hkLe : kVal ≤ p :=
    Nat.le_of_lt hkLt
  let k : Fin p := ⟨kVal, hkLt⟩
  /-
  j.isLt は `j.1 < r` なので、
  word length への上界は hALen / hBLen を経由して作る。
  -/
  have hJLtA :
      j.1 < A.word.length := by
    rw [hALen]
    exact j.isLt
  have hJLtB :
      j.1 < B.word.length := by
    rw [hBLen]
    exact j.isLt
  have hJLeA :
      j.1 ≤ A.word.length :=
    Nat.le_of_lt hJLtA
  have hJLeB :
      j.1 ≤ B.word.length :=
    Nat.le_of_lt hJLtB
  have hxDepth :
      x.height kVal =
        twoSteps pre +
          prefixTwoDepth A.word j.1 := by
    unfold FiberPoint.height
    rw [hx]
    exact
      prefixTwoDepth_splice_middle
        pre A.word post hJLeA
  have hyDepth :
      y.height kVal =
        twoSteps pre +
          prefixTwoDepth B.word j.1 := by
    unfold FiberPoint.height
    rw [hy]
    exact
      prefixTwoDepth_splice_middle
        pre B.word post hJLeB
  /-
  local one-cell deletion をまず local prefix depth の
  exact one-step lowering に変換する。
  -/
  have hLocalExact :
      B.toFiberPoint.excessAt j.1 + 1 =
        A.toFiberPoint.excessAt j.1 := by
    exact hjExact
  have hLocalDepthExact :
      prefixTwoDepth B.word j.1 + 1 =
        prefixTwoDepth A.word j.1 := by
    exact
      localDecoration_prefixTwoDepth_add_one_eq_of_excessAt_add_one_eq
        A B
        (Nat.le_of_lt j.isLt)
        hLocalExact
  /-
  splice の共通 prefix を付けても height の exact one-step lowering は保存される。
  -/
  have hGlobalHeightExact :
      y.height kVal + 1 =
        x.height kVal := by
    rw [hyDepth, hxDepth]
    omega
  /-
  同じ global index なので、height の one-step lowering を
  excess の one-step lowering に移す。
  -/
  have hGlobalExact :
      y.excessAt kVal + 1 =
        x.excessAt kVal := by
    exact
      fiberPoint_excessAt_add_one_eq_of_height_add_one_eq
        hkLe hGlobalHeightExact
  have hOtherGlobal :
      ∀ q : Fin p, q ≠ k →
        y.toFerrersShape.column q =
          x.toFerrersShape.column q := by
    intro q hqk
    let qv : ℕ := q.1
    have hqLe : qv ≤ p := by
      dsimp [qv]
      exact Nat.le_of_lt q.isLt
    by_cases hBefore : qv < pre.length
    /-
    changed block より完全に左。
    splice の prefix depth はそのまま同じ。
    -/
    · have hDepth :
          x.height qv = y.height qv := by
        unfold FiberPoint.height
        rw [hx, hy]
        exact
          prefixTwoDepth_splice_eq_of_before
            pre A.word B.word post
            (Nat.le_of_lt hBefore)
      change
        y.excessAt qv =
          x.excessAt qv
      exact
        fiberPoint_excessAt_eq_of_height_eq
          (x := y) (y := x)
          hqLe hDepth.symm
    · have hInsideLower :
          pre.length ≤ qv :=
        Nat.le_of_not_gt hBefore
      by_cases hAfter : pre.length + r ≤ qv
      /-
      changed block より完全に右。
      A / B は length と total twoSteps が同じなので、
      splice 後の prefix depth も同じ。
      -/
      · have hDepth :
            x.height qv = y.height qv := by
          unfold FiberPoint.height
          rw [hx, hy]
          apply
            prefixTwoDepth_splice_eq_of_after
              pre A.word B.word post
          · exact hALen.trans hBLen.symm
          · exact hTwo
          · simpa [hALen] using hAfter
        change
          y.excessAt qv =
            x.excessAt qv
        exact
          fiberPoint_excessAt_eq_of_height_eq
            (x := y) (y := x)
            hqLe hDepth.symm
      /-
      changed block の内部。
      qv を local coordinate t に戻す。
      -/
      · have hUpper :
            qv < pre.length + r :=
          Nat.lt_of_not_ge hAfter
        have hInsideUpper :
            qv - pre.length < r := by
          omega
        let t : Fin r :=
          ⟨qv - pre.length, hInsideUpper⟩
        have hReconstruct :
            pre.length + (qv - pre.length) = qv :=
          Nat.add_sub_of_le hInsideLower
        /-
        q ≠ changed global column なので、
        local coordinate t も changed local column j とは異なる。
        -/
        have htNe : t ≠ j := by
          intro htj
          have hv :
              t.1 = j.1 :=
            congrArg Fin.val htj
          dsimp [t] at hv
          have hqEq :
              qv = pre.length + j.1 := by
            calc
              qv =
                  pre.length + (qv - pre.length) :=
                hReconstruct.symm
              _ =
                  pre.length + j.1 := by
                rw [hv]
          apply hqk
          apply Fin.ext
          simpa [qv, k, kVal] using hqEq
        have hLocEq :
            B.toFiberPoint.excessAt t.1 =
              A.toFiberPoint.excessAt t.1 := by
          exact hjOnly t htNe
        have hTLeA :
            t.1 ≤ A.word.length := by
          rw [hALen]
          exact Nat.le_of_lt t.isLt
        have hTLeB :
            t.1 ≤ B.word.length := by
          rw [hBLen]
          exact Nat.le_of_lt t.isLt
        /-
        global qv と local coordinate t の exact index relation。
        ここを omega に任せず Nat.add_sub_of_le で固定する。
        -/
        have hIndexEq :
            pre.length + t.1 = qv := by
          dsimp [t]
          exact hReconstruct
        have hxDepth' :
            x.height qv =
              twoSteps pre +
                prefixTwoDepth A.word t.1 := by
          unfold FiberPoint.height
          rw [hx, ← hIndexEq]
          exact
            prefixTwoDepth_splice_middle
              pre A.word post hTLeA
        have hyDepth' :
            y.height qv =
              twoSteps pre +
                prefixTwoDepth B.word t.1 := by
          unfold FiberPoint.height
          rw [hy, ← hIndexEq]
          exact
            prefixTwoDepth_splice_middle
              pre B.word post hTLeB
        /-
        t ≠ j なので local excess は不変。
        まず local prefix depth の不変性へ移す。
        -/
        have hLocalDepthEq :
            prefixTwoDepth B.word t.1 =
              prefixTwoDepth A.word t.1 := by
          exact
            localDecoration_prefixTwoDepth_eq_of_excessAt_eq
              B A
              (Nat.le_of_lt t.isLt)
              hLocEq
        /-
        共通 prefix を付け戻して global height equality を得る。
        -/
        have hDepth :
            y.height qv =
              x.height qv := by
          calc
            y.height qv =
                twoSteps pre +
                  prefixTwoDepth B.word t.1 :=
              hyDepth'
            _ =
                twoSteps pre +
                  prefixTwoDepth A.word t.1 := by
              rw [hLocalDepthEq]
            _ =
                x.height qv :=
              hxDepth'.symm
        change
          y.excessAt qv =
            x.excessAt qv
        exact
          fiberPoint_excessAt_eq_of_height_eq
            (x := y) (y := x)
            hqLe hDepth
  apply
    FerrersShape.isUnitCover_of_unique_lowering k
  · change
      y.excessAt kVal + 1 =
        x.excessAt kVal
    exact hGlobalExact
  · exact hOtherGlobal

/-! ## 6. fixed-skeleton product relation と actual Ferrers relation -/

/--
同じ fixed skeleton 上の actual genuine one-cell Ferrers deletion。
元 top source の decoration interval に依存しない中立な relation。
-/
def FixedSkeletonActualCellDeletion
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X Y : FixedSkeletonSource P u D) : Prop :=
  FerrersShape.IsUnitCover
    Y.1.toFerrersShape X.1.toFerrersShape

namespace FixedSkeletonProductCellDeletion

/--
## Product -> Actual Compatibility

one-factor-at-a-time の product deletion は、actual whole Ferrers geometry 上でも exact one-cell deletion。
-/
theorem toActualCellDeletion
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonProductCellDeletion X Y) :
    FixedSkeletonActualCellDeletion X Y := by
  unfold FixedSkeletonProductCellDeletion at h
  let S := h.exists_split
  have hXWord :=
    X.word_eq_anchor_append_blocks
      P hPrimitive hReduced u D
  have hYWord :=
    Y.word_eq_anchor_append_blocks
      P hPrimitive hReduced u D
  have hXSplice :
      X.1.word =
        (fixedSkeletonAnchor u ++ S.pre.flatten) ++
          S.A.word ++ S.post.flatten := by
    rw [hXWord, S.source_blocks]
    simp [List.append_assoc]
  have hYSplice :
      Y.1.word =
        (fixedSkeletonAnchor u ++ S.pre.flatten) ++
          S.B.word ++ S.post.flatten := by
    rw [hYWord, S.target_blocks]
    simp [List.append_assoc]
  unfold FixedSkeletonActualCellDeletion
  exact FiberPoint.isUnitCover_of_localDecorationSplice
    X.1 Y.1
    (fixedSkeletonAnchor u ++ S.pre.flatten)
    S.post.flatten
    S.A S.B
    hXSplice hYSplice S.local_step

end FixedSkeletonProductCellDeletion

/-! ## 7. arbitrary actual one-cell cover も一つの genuine common RecordBlock に support を持つ -/

namespace FixedSkeletonActualCellDeletion

/-- fixed-skeleton actual one-cell cover の唯一 changed column。 -/
theorem exists_unique_changed_column
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonActualCellDeletion X Y) :
    ∃ k : Fin P.oddCount,
      Y.1.toFerrersShape.column k + 1 =
        X.1.toFerrersShape.column k ∧
      ∀ j : Fin P.oddCount, j ≠ k →
        Y.1.toFerrersShape.column j =
          X.1.toFerrersShape.column j := by
  unfold FixedSkeletonActualCellDeletion at h
  exact FerrersShape.IsUnitCover.exists_unique_changed_column h

/--
## Actual fixed-skeleton compact support

同じ record length skeleton を持つ二 actual states の whole Ferrers one-cell cover は、
その唯一 changed column を strict interior に含む共通 genuine RecordBlock を持ち、
その block の open interval 外では displacement が exact に 0。
-/
theorem exists_proper_recordBlock_support
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonActualCellDeletion X Y) :
    ∃ k : Fin P.oddCount,
      ∃ a len : ℕ,
        RecordBlock X.1 a len ∧
        RecordBlock Y.1 a len ∧
        a < k.1 ∧
        k.1 < a + len ∧
        BlockReplacement X.1 Y.1 a (a + len) := by
  rcases h.exists_unique_changed_column with
    ⟨k, hkExact, hkOnly⟩
  have hChanged :
      Y.1.toFerrersShape.column k < X.1.toFerrersShape.column k := by
    omega
  have hLenXY :
      Y.decomposition.lengths = X.decomposition.lengths := by
    exact Y.decomposition_lengths.trans X.decomposition_lengths.symm
  have CY : RecordChain Y.1 1 X.decomposition.lengths := by
    have hCY := Y.decomposition.chain
    rw [hLenXY] at hCY
    exact hCY
  have hkPos : 0 < k.1 := by
    by_contra hnot
    have hk0 : k.1 = 0 := by omega
    have hZeroY := Y.1.toFerrersShape_first_zero P.oddCount_pos
    have hZeroX := X.1.toFerrersShape_first_zero P.oddCount_pos
    have hkFin : k = ⟨0, P.oddCount_pos⟩ := by
      apply Fin.ext
      exact hk0
    rw [hkFin, hZeroY, hZeroX] at hChanged
    omega
  rcases
      RecordChain.exists_common_block_strictly_containing_changed_column
        X.decomposition.chain CY (k := k) (by omega) hChanged with
    ⟨a, len, BX, BY, hak, hkb⟩
  have hReplacement : BlockReplacement X.1 Y.1 a (a + len) := by
    refine {
      start_lt_stop := Nat.lt_add_of_pos_right BX.length_pos
      stop_le_terminal := BX.end_le_terminal
      outside := ?_
    }
    intro j hjp hOutside
    by_cases hjTerm : j = P.oddCount
    · subst j
      exact profileDisplacement_terminal X.1 Y.1
    · have hjLt : j < P.oddCount := by omega
      have hjNeKVal : j ≠ k.1 := by
        intro hEq
        subst j
        rcases hOutside with hLeft | hRight
        · omega
        · omega
      have hjNeK : (⟨j, hjLt⟩ : Fin P.oddCount) ≠ k := by
        intro hEq
        exact hjNeKVal (congrArg Fin.val hEq)
      have hCol := hkOnly ⟨j, hjLt⟩ hjNeK
      apply profileDisplacement_eq_zero_of_ferrersColumn_eq hjLt
      exact hCol.symm
  exact ⟨k, a, len, BX, BY, hak, hkb, hReplacement⟩

/-- compact support の存在だけを短く取り出す。 -/
theorem blockReplacement_on_some_recordBlock
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonActualCellDeletion X Y) :
    ∃ a len : ℕ,
      RecordBlock X.1 a len ∧
      RecordBlock Y.1 a len ∧
      BlockReplacement X.1 Y.1 a (a + len) := by
  rcases h.exists_proper_recordBlock_support with
    ⟨_k, a, len, BX, BY, _hak, _hkb, hRep⟩
  exact ⟨a, len, BX, BY, hRep⟩

end FixedSkeletonActualCellDeletion

/-- product deletion には actual common-record-block compact support がある。 -/
theorem FixedSkeletonProductCellDeletion.exists_proper_recordBlock_support
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonProductCellDeletion X Y) :
    ∃ k : Fin P.oddCount,
      ∃ a len : ℕ,
        RecordBlock X.1 a len ∧
        RecordBlock Y.1 a len ∧
        a < k.1 ∧
        k.1 < a + len ∧
        BlockReplacement X.1 Y.1 a (a + len) :=
  (h.toActualCellDeletion
    (hPrimitive := hPrimitive)
    (hReduced := hReduced)).exists_proper_recordBlock_support

/-! ## 8. BoundaryDecoration の各 fixed base fiber への specialization -/

/-- boundary base `R` の actual fiber 内の genuine Ferrers one-cell deletion。 -/
def BoundaryDecorationActualFiberCellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) : Prop :=
  FixedSkeletonActualCellDeletion X Y

/-- boundary actual fiber 内の transported product step。 -/
noncomputable def BoundaryDecorationActualFiberProductCellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) : Prop :=
  FixedSkeletonProductCellDeletion X Y

/-- 各 boundary fiber でも product step は genuine actual Ferrers one-cell deletion。 -/
theorem boundaryDecorationActualFiberProductCellDeletion_to_actual
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R}
    (h : BoundaryDecorationActualFiberProductCellDeletion
      P hPrimitive hReduced u D R X Y) :
    BoundaryDecorationActualFiberCellDeletion
      P hPrimitive hReduced u D R X Y := by
  exact FixedSkeletonProductCellDeletion.toActualCellDeletion
    (hPrimitive := hPrimitive)
    (hReduced := hReduced)
    h

/-- 各 boundary fiber の product step は一つの genuine coarse RecordBlock 内に support を持つ。 -/
theorem boundaryDecorationActualFiberProductCellDeletion_compactSupport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R}
    (h : BoundaryDecorationActualFiberProductCellDeletion
      P hPrimitive hReduced u D R X Y) :
    ∃ k : Fin P.oddCount,
      ∃ a len : ℕ,
        RecordBlock X.1 a len ∧
        RecordBlock Y.1 a len ∧
        a < k.1 ∧
        k.1 < a + len ∧
        BlockReplacement X.1 Y.1 a (a + len) := by
  exact FixedSkeletonProductCellDeletion.exists_proper_recordBlock_support
    (hPrimitive := hPrimitive)
    (hReduced := hReduced)
    h

/--
abstract boundary-decoration fiber 上の one-cell relation。
actual fiber equivalence で戻した二点の transported product step として定義する。
-/
noncomputable def BoundaryDecorationFiberCellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (A B : BoundaryDecorationFiber D R) : Prop :=
  BoundaryDecorationActualFiberProductCellDeletion
    P hPrimitive hReduced u D R
    ((boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm A)
    ((boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm B)

/-- abstract fiber one-cell step の actual realizations は genuine whole Ferrers unit cover。 -/
theorem boundaryDecorationFiberCellDeletion_realization_unitCover
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {A B : BoundaryDecorationFiber D R}
    (h : BoundaryDecorationFiberCellDeletion
      P hPrimitive hReduced u D R A B) :
    FerrersShape.IsUnitCover
      (((boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R).symm B).1.toFerrersShape)
      (((boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R).symm A).1.toFerrersShape) := by
  exact boundaryDecorationActualFiberProductCellDeletion_to_actual
    P hPrimitive hReduced u D R h

/-- abstract fiber one-cell step の actual realization は genuine common RecordBlock support を持つ。 -/
theorem boundaryDecorationFiberCellDeletion_realization_compactSupport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {A B : BoundaryDecorationFiber D R}
    (h : BoundaryDecorationFiberCellDeletion
      P hPrimitive hReduced u D R A B) :
    ∃ k : Fin P.oddCount,
      ∃ a len : ℕ,
        RecordBlock
          ((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm A).1 a len ∧
        RecordBlock
          ((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm B).1 a len ∧
        a < k.1 ∧
        k.1 < a + len ∧
        BlockReplacement
          ((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm A).1
          ((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm B).1
          a (a + len) := by
  exact boundaryDecorationActualFiberProductCellDeletion_compactSupport
    P hPrimitive hReduced u D R h

/-! ## 9. closure package -/

/--
fiber deletion actual compatibility 層で閉じた内容。
-/
structure BoundaryDecorationFiberDeletionActualCompatibilityClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  product_step_is_actual :
    ∀ (R : RetainedBoundaryPattern D)
      (X Y : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      BoundaryDecorationActualFiberProductCellDeletion
          P hPrimitive hReduced u D R X Y →
        BoundaryDecorationActualFiberCellDeletion
          P hPrimitive hReduced u D R X Y
  product_step_compact :
    ∀ (R : RetainedBoundaryPattern D)
      (X Y : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      BoundaryDecorationActualFiberProductCellDeletion
          P hPrimitive hReduced u D R X Y →
        ∃ k : Fin P.oddCount,
          ∃ a len : ℕ,
            RecordBlock X.1 a len ∧
            RecordBlock Y.1 a len ∧
            a < k.1 ∧
            k.1 < a + len ∧
            BlockReplacement X.1 Y.1 a (a + len)
  abstract_step_actual :
    ∀ (R : RetainedBoundaryPattern D)
      (A B : BoundaryDecorationFiber D R),
      BoundaryDecorationFiberCellDeletion
          P hPrimitive hReduced u D R A B →
        FerrersShape.IsUnitCover
          (((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm B).1.toFerrersShape)
          (((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm A).1.toFerrersShape)

/-- Fiber deletion actual compatibility closure theorem。 -/
theorem boundaryDecorationFiberDeletionActualCompatibility_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationFiberDeletionActualCompatibilityClosed
      P hPrimitive hReduced u D := by
  refine {
    product_step_is_actual := ?_
    product_step_compact := ?_
    abstract_step_actual := ?_
  }
  · intro R X Y h
    exact boundaryDecorationActualFiberProductCellDeletion_to_actual
      P hPrimitive hReduced u D R h
  · intro R X Y h
    exact boundaryDecorationActualFiberProductCellDeletion_compactSupport
      P hPrimitive hReduced u D R h
  · intro R A B h
    exact boundaryDecorationFiberCellDeletion_realization_unitCover
      P hPrimitive hReduced u D R h

end RecordFerrers
end Collatz2
