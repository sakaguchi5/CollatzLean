import CollatzLean.Collatz2.RecordFerrers.Perturbation.P27DirectRecordRunMerge

/-!
# Record–Ferrers 摂動理論 28: 標準分解の粗視化と一ブロック正規化

P27 では、連続する Record 区間を左端 roof の高さへ平坦化することで、
その区間全体を一つの RecordBlock へ直接併合できることを示した。

本ファイルでは、その局所併合を RecordDecomposition 全体へ貼り戻す。

まず、0 個以上の interior RecordBlock からなる「左側区間」を導入する。
これにより

  左側の列 ++ 併合する連続区間 ++ 右側の列

という分割を明示し、中央だけを P27 で平坦化したあと、左右の RecordBlock を保存して

  左側の列 ++ [中央の長さ和] ++ 右側の列

という target RecordDecomposition を構成する。

終端側の連続区間についても同様に、左側の列を保ったまま終端までを一つへ併合する。

最後に cut 1 からの RecordDecomposition 全体を P27 の terminal 直接併合へ渡すことで、
一回の actual fixed-chord deformation だけで標準骨格 `[p-1]` を持つ target を得る。
これは defect split や `p > 3` を必要としない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
0 個以上の interior RecordBlock からなる左側区間。
空の場合は開始点と終了点が同じ。
-/
inductive RecordLeftSegment
    {p H : ℕ}
    (u : FiberPoint p H) : ℕ → List ℕ → ℕ → Type
  | empty
      {start : ℕ} :
      RecordLeftSegment u start [] start
  | cons
      {start len stop : ℕ}
      {rest : List ℕ}
      (block : RecordBlock u start len)
      (blockInterior : start + len < p)
      (tail : RecordLeftSegment u (start + len) rest stop) :
      RecordLeftSegment u start (len :: rest) stop

namespace RecordLeftSegment

/-- 左側区間の長さ和は終了点までの距離。 -/
theorem start_add_sum_eq_stop
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (S : RecordLeftSegment u start lengths stop) :
    start + lengths.sum = stop := by
  induction S with
  | empty => simp
  | cons B hInterior T ih =>
      simp only [List.sum_cons]
      omega

/-- 左側区間の終了点は開始点以後。 -/
theorem start_le_stop
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (S : RecordLeftSegment u start lengths stop) :
    start ≤ stop := by
  have h := S.start_add_sum_eq_stop
  omega

/--
左側区間の後ろに terminal までの RecordChain を接続する。
-/
theorem attachChain
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {leftLengths rightLengths : List ℕ}
    (S : RecordLeftSegment u start leftLengths stop)
    (C : RecordChain u stop rightLengths) :
    RecordChain u start (leftLengths ++ rightLengths) := by
  induction S with
  | empty =>
      simpa using C
  | @cons start len stop rest B hInterior T ih =>
      change RecordChain u start (len :: (rest ++ rightLengths))
      exact RecordChain.cons B hInterior (ih C)

/-- replacement 区間の完全な左側にある左側区間は保存される。 -/
noncomputable def preserved_on_left
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (BRep : BlockReplacement u v a c)
    {start stop : ℕ}
    {lengths : List ℕ}
    (S : RecordLeftSegment u start lengths stop)
    (hLeft : stop ≤ a) :
    RecordLeftSegment v start lengths stop := by
  induction S with
  | empty =>
      exact RecordLeftSegment.empty
  | @cons start len stop rest B hInterior T ih =>
      apply RecordLeftSegment.cons
      · apply B.preserved_on_left BRep
        have hTail := T.start_add_sum_eq_stop
        omega
      · exact hInterior
      · exact ih hLeft

/-- replacement 区間の完全な右側にある左側区間も保存される。 -/
noncomputable def preserved_on_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (BRep : BlockReplacement u v a c)
    {start stop : ℕ}
    {lengths : List ℕ}
    (S : RecordLeftSegment u start lengths stop)
    (hRight : c ≤ start) :
    RecordLeftSegment v start lengths stop := by
  induction S with
  | empty =>
      exact RecordLeftSegment.empty
  | @cons start len stop rest B hInterior T ih =>
      apply RecordLeftSegment.cons
      · exact B.preserved_on_right BRep hRight
      · exact hInterior
      · exact ih (by omega)

end RecordLeftSegment

namespace RecordChain

/-- replacement 区間の完全な右側にある RecordChain 全体は保存される。 -/
theorem preserved_on_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (BRep : BlockReplacement u v a c)
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hRight : c ≤ start) :
    RecordChain v start lengths := by
  induction C with
  | last B hTerminal =>
      exact RecordChain.last
        (B.preserved_on_right BRep hRight) hTerminal
  | @cons start len rest B hInterior T ih =>
      exact RecordChain.cons
        (B.preserved_on_right BRep hRight)
        hInterior
        (ih (by omega))

end RecordChain

/--
中央の interior Record 区間を一つへ併合するための全体分割。

source length list は

  leftLengths ++ middleLengths ++ rightLengths

と書ける。
-/
structure InteriorCoarseningWindow
    {p H : ℕ}
    {u : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition u start)
    (leftLengths middleLengths rightLengths : List ℕ) : Type where
  leftStop : ℕ
  middleStop : ℕ
  leftPart : RecordLeftSegment u start leftLengths leftStop
  middlePart : InteriorRecordRun u leftStop middleLengths middleStop
  rightPart : RecordChain u middleStop rightLengths
  sourceLengths :
    D.lengths = (leftLengths ++ middleLengths) ++ rightLengths

/--
終端側の連続 Record 区間を一つへ併合するための全体分割。
-/
structure TerminalCoarseningWindow
    {p H : ℕ}
    {u : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition u start)
    (leftLengths tailLengths : List ℕ) : Type where
  cut : ℕ
  leftPart : RecordLeftSegment u start leftLengths cut
  tailPart : RecordChain u cut tailLengths
  sourceLengths :
    D.lengths = leftLengths ++ tailLengths

/-- 一つの連続区間を一要素へまとめた長さ列。 -/
def coarsenedLengths
    (leftLengths middleLengths rightLengths : List ℕ) : List ℕ :=
  (leftLengths ++ [middleLengths.sum]) ++ rightLengths

@[simp] theorem coarsenedLengths_length
    (leftLengths middleLengths rightLengths : List ℕ) :
    (coarsenedLengths leftLengths middleLengths rightLengths).length =
      leftLengths.length + 1 + rightLengths.length := by
  simp [coarsenedLengths]
  omega

/-- 中央に二ブロック以上あれば、粗視化後のブロック数は strict に減る。 -/
theorem coarsenedLengths_length_lt
    {leftLengths middleLengths rightLengths : List ℕ}
    (hTwo : 2 ≤ middleLengths.length) :
    (coarsenedLengths leftLengths middleLengths rightLengths).length <
      ((leftLengths ++ middleLengths) ++ rightLengths).length := by
  simp [coarsenedLengths]
  omega

/--
## 主定理 1: interior の連続区間を全体 RecordDecomposition へ貼り戻す

中央区間だけを P27 で平坦化し、左側区間と右側 chain を保存する。
-/
theorem directInteriorCoarsening
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    {start : ℕ}
    (D : RecordDecomposition u start)
    {leftLengths middleLengths rightLengths : List ℕ}
    (W : InteriorCoarseningWindow D leftLengths middleLengths rightLengths) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ E : RecordDecomposition v start,
        BlockReplacement u v W.leftStop W.middleStop ∧
        E.lengths =
          coarsenedLengths leftLengths middleLengths rightLengths ∧
        D.lengths = (leftLengths ++ middleLengths) ++ rightLengths := by
  obtain ⟨v, hRep, hFv, hMerged⟩ :=
    directInteriorRecordRunMerge
      P hPrimitive hReduced u D.whole_firstCrossing W.middlePart
  have hLeftSaved :
      RecordLeftSegment v start leftLengths W.leftStop :=
    W.leftPart.preserved_on_left hRep le_rfl
  have hRightSaved :
      RecordChain v W.middleStop rightLengths :=
    W.rightPart.preserved_on_right hRep le_rfl
  have hMiddleEnd :
      W.leftStop + middleLengths.sum = W.middleStop :=
    W.middlePart.start_add_sum_eq_stop
  have hMiddleInterior :
      W.leftStop + middleLengths.sum < P.oddCount := by
    rw [hMiddleEnd]
    exact W.middlePart.stop_lt_terminal
  have hRightSaved' :
      RecordChain v (W.leftStop + middleLengths.sum) rightLengths := by
    rw [hMiddleEnd]
    exact hRightSaved
  let middleAndRight :
      RecordChain v W.leftStop (middleLengths.sum :: rightLengths) :=
    RecordChain.cons hMerged hMiddleInterior hRightSaved'
  let wholeChain :
      RecordChain v start
        (leftLengths ++ (middleLengths.sum :: rightLengths)) :=
    hLeftSaved.attachChain middleAndRight
  let E : RecordDecomposition v start := {
    lengths := leftLengths ++ (middleLengths.sum :: rightLengths)
    chain := wholeChain
    whole_firstCrossing := hFv
  }
  refine ⟨v, E, hRep, ?_, W.sourceLengths⟩
  dsimp [E, coarsenedLengths]
  simp [List.append_assoc]

/--
## 主定理 2: terminal 側の連続区間を全体 RecordDecomposition へ貼り戻す

左側区間を保存し、cut 以後を P27 で一つの terminal RecordBlock へ併合する。
-/
theorem directTerminalCoarsening
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    {start : ℕ}
    (D : RecordDecomposition u start)
    {leftLengths tailLengths : List ℕ}
    (W : TerminalCoarseningWindow D leftLengths tailLengths)
    (hCutPos : 0 < W.cut) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ E : RecordDecomposition v start,
        BlockReplacement u v W.cut P.oddCount ∧
        E.lengths = leftLengths ++ [tailLengths.sum] ∧
        D.lengths = leftLengths ++ tailLengths := by
  obtain ⟨v, hRep, hFv, hMerged⟩ :=
    directTerminalRecordRunMerge
      P hPrimitive hReduced u D.whole_firstCrossing
      W.tailPart hCutPos
  have hLeftSaved :
      RecordLeftSegment v start leftLengths W.cut :=
    W.leftPart.preserved_on_left hRep le_rfl
  have hTerminal : W.cut + tailLengths.sum = P.oddCount :=
    W.tailPart.start_add_sum_eq_terminal
  let tailChain : RecordChain v W.cut [tailLengths.sum] :=
    RecordChain.last hMerged hTerminal
  let wholeChain :
      RecordChain v start (leftLengths ++ [tailLengths.sum]) :=
    hLeftSaved.attachChain tailChain
  let E : RecordDecomposition v start := {
    lengths := leftLengths ++ [tailLengths.sum]
    chain := wholeChain
    whole_firstCrossing := hFv
  }
  exact ⟨v, E, hRep, rfl, W.sourceLengths⟩

/-- terminal 側に二ブロック以上あれば、上の粗視化はブロック数を減らす。 -/
theorem terminalCoarsening_length_lt
    {p H : ℕ}
    {u : FiberPoint p H}
    {start : ℕ}
    {D : RecordDecomposition u start}
    {leftLengths tailLengths : List ℕ}
    (W : TerminalCoarseningWindow D leftLengths tailLengths)
    (hTwo : 2 ≤ tailLengths.length) :
    (leftLengths ++ [tailLengths.sum]).length < D.lengths.length := by
  rw [W.sourceLengths]
  simp
  omega

/-- cut 1 から見た一ブロック標準形。 -/
def OneBlockNormalForm
    (P : Word.ContractingExponentPair)
    (v : FiberPoint P.oddCount P.twoDepth) : Prop :=
  ∃ E : RecordDecomposition v 1,
    E.lengths = [P.oddCount - 1]

/-- 一ブロック標準形では、任意の標準分解の長さ列も `[p-1]`。 -/
theorem OneBlockNormalForm.lengths_eq
    {P : Word.ContractingExponentPair}
    {v : FiberPoint P.oddCount P.twoDepth}
    (N : OneBlockNormalForm P v)
    (E : RecordDecomposition v 1) :
    E.lengths = [P.oddCount - 1] := by
  rcases N with ⟨D, hD⟩
  calc
    E.lengths = D.lengths := E.lengths_unique D
    _ = [P.oddCount - 1] := hD

/--
## 主定理 3: 与えられた cut 1 標準分解を一回で `[p-1]` へ正規化

P27 の terminal 直接併合を decomposition 全体に一度だけ適用する。
-/
theorem directOneBlockNormalization
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      BlockReplacement u v 1 P.oddCount ∧
      FirstCrossing v.word ∧
      OneBlockNormalForm P v := by
  obtain ⟨v, hRep, hFv, hMerged⟩ :=
    directTerminalRecordRunMerge
      P hPrimitive hReduced u D.whole_firstCrossing
      D.chain (by omega)
  have hCover : 1 + D.lengths.sum = P.oddCount :=
    D.start_add_sum_eq_terminal
  have hSum : D.lengths.sum = P.oddCount - 1 := by
    omega
  let E : RecordDecomposition v 1 := {
    lengths := [D.lengths.sum]
    chain := RecordChain.last hMerged hCover
    whole_firstCrossing := hFv
  }
  refine ⟨v, hRep, hFv, ?_⟩
  refine ⟨E, ?_⟩
  dsimp [E]
  rw [hSum]

/--
## 主定理 4: primitive + StripReduced FirstCrossing fiber は一ブロック標準形へ直接到達する

source decomposition 自体も P20 から自動的に取る。
`p > 3` や defect split は不要で、`p > 1` だけでよい。
-/
theorem exists_directOneBlockNormalization_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    (hp : 1 < P.oddCount) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      BlockReplacement u v 1 P.oddCount ∧
      FirstCrossing v.word ∧
      OneBlockNormalForm P v := by
  obtain ⟨D⟩ :=
    exists_recordDecomposition_one_of_primitiveReduced
      P hPrimitive hReduced u hFu hp
  exact directOneBlockNormalization
    P hPrimitive hReduced u D

/--
一ブロック正規化 target の標準骨格は canonical に `[p-1]` である。
-/
theorem exists_directOneBlockNormalization_with_unique_lengths
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    (hp : 1 < P.oddCount) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      BlockReplacement u v 1 P.oddCount ∧
      FirstCrossing v.word ∧
      (∀ E : RecordDecomposition v 1,
        E.lengths = [P.oddCount - 1]) := by
  obtain ⟨v, hRep, hFv, hNormal⟩ :=
    exists_directOneBlockNormalization_of_primitiveReduced
      P hPrimitive hReduced u hFu hp
  refine ⟨v, hRep, hFv, ?_⟩
  intro E
  exact hNormal.lengths_eq E

end RecordFerrers
end Collatz2
