import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationCanonicalMergeActualCompatibility

/-!
# Record–Ferrers Perturbation / Canonical Merge Compact Support

`BoundaryDecorationCanonicalMergeActualCompatibility` では、P27 `flatIntervalTarget` が
compact-support replacement であり、merged interval の local decoration area が 0 になること、
さらに canonical area-vector formula を持つ actual target は canonical actual target に一意であることを示した。

本ファイルでは genuine one-boundary deletion に対して、その comparison port を実際に閉じる。

中心となる考えは次の通り。

* `R b = true` なら、`R -> eraseRetainedBoundary R b` の relative flags には false がちょうど一つだけ現れる。
* RecordChain をその relative flags に沿って左から読む。
* true の間は現在の RecordBlock をそのまま保存する。
* 唯一の false に到達したところで、その境界を挟む source の隣接二 RecordBlock だけを
  P27 `flatIntervalTarget` で直接平坦化する。
* その target は区間外を exact に保存し、二 block を一つの genuine RecordBlock へ merge し、
  merged local area を exact に 0 にする。
* 得られた target の local-area vector は `canonicalCoarsenValues` と一致するため、
  compatibility 層の uniqueness により canonical actual inter-fiber merge そのものに一致する。

従って genuine one-boundary canonical merge は、abstract product-coordinate contraction であると同時に、
actual Ferrers geometry 上では削除境界を挟む隣接二 RecordBlock の外端だけを support に持つ
P27 型 compact-support flattening そのものである。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. Bool 列の「false がちょうど一つ」 -/

/-- Bool 列の全成分が true。 -/
def BoolListAllTrue (xs : List Bool) : Prop :=
  ∀ x ∈ xs, x = true

/--
Bool 列に false がちょうど一つだけ現れることを、coarsening recursion と同じ向きで表す。

`head` は唯一の false が先頭、`tail` は先頭 true を読み飛ばして tail に唯一の false がある場合。
-/
inductive ExactlyOneFalse : List Bool → Prop
  | head {xs : List Bool} (hTail : BoolListAllTrue xs) :
      ExactlyOneFalse (false :: xs)
  | tail {xs : List Bool} (h : ExactlyOneFalse xs) :
      ExactlyOneFalse (true :: xs)

namespace ExactlyOneFalse

/-- exactly-one-false list は空ではない。 -/
theorem ne_nil {xs : List Bool} (h : ExactlyOneFalse xs) : xs ≠ [] := by
  cases h <;> simp

end ExactlyOneFalse

/-- all-true flags は length skeleton を変えない。 -/
theorem coarsenByFlags_eq_self_of_allTrue
    (lengths : List ℕ)
    (flags : List Bool)
    (hTrue : BoolListAllTrue flags) :
    coarsenByFlags lengths flags = lengths := by
  induction lengths generalizing flags with
  | nil =>
      simp [coarsenByFlags]
  | cons r rest ih =>
      cases rest with
      | nil =>
          simp [coarsenByFlags]
      | cons s tail =>
          cases flags with
          | nil =>
              rfl
          | cons b bs =>
              have hb : b = true := hTrue b (by simp)
              subst b
              have hTail : BoolListAllTrue bs := by
                intro x hx
                exact hTrue x (by simp [hx])
              rw [coarsenByFlags_cons_true r (by simp) bs]
              rw [ih bs hTail]

/-- all-true flags は pure area vector も変えない。 -/
theorem LocalAreaTuple.canonicalCoarsenValues_eq_self_of_allTrue
    (values : List ℕ)
    (flags : List Bool)
    (hTrue : BoolListAllTrue flags) :
    LocalAreaTuple.canonicalCoarsenValues values flags = values := by
  induction values generalizing flags with
  | nil =>
      simp [LocalAreaTuple.canonicalCoarsenValues]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [LocalAreaTuple.canonicalCoarsenValues]
      | cons b tail =>
          cases flags with
          | nil =>
              rfl
          | cons keep more =>
              have hk : keep = true := hTrue keep (by simp)
              subst keep
              have hMore : BoolListAllTrue more := by
                intro x hx
                exact hTrue x (by simp [hx])
              simp only [LocalAreaTuple.canonicalCoarsenValues]
              rw [ih more hMore]

/--
同じ Bool 列の一つの true だけを false にした関係。
relative flags の exactly-one-false 性を list recursion だけで証明するための補助関係。
-/
inductive OneTrueToFalse : List Bool → List Bool → Prop
  | here {xs : List Bool} :
      OneTrueToFalse (true :: xs) (false :: xs)
  | there {u : Bool} {xs ys : List Bool}
      (h : OneTrueToFalse xs ys) :
      OneTrueToFalse (u :: xs) (u :: ys)

namespace BoolListAllTrue

/--
all-true Bool 列の先頭に `true` を追加しても all-true。

`relativeBoundaryFlagsList` の self case で、
保持された先頭 boundary が relative flag `true` として残る場合に使う。
-/
theorem cons_true
    {xs : List Bool}
    (h : BoolListAllTrue xs) :
    BoolListAllTrue (true :: xs) := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with hxHead | hxTail
  · exact hxHead
  · exact h x hxTail

end BoolListAllTrue

/--
self-relative flags は全成分 `true`。

元の flag が `false` の位置は upper 側ですでに削除済みなので
relative flag list には現れない。
元の flag が `true` の位置だけが relative flag `true` として残る。

したがって同じ boundary pattern への relative coarsening は
残っている全 boundary を保持する all-true flags になる。
-/
theorem relativeBoundaryFlagsList_self_allTrue
    (xs : List Bool) :
    BoolListAllTrue (relativeBoundaryFlagsList xs xs) := by
  induction xs with
  | nil =>
      simp [BoolListAllTrue, relativeBoundaryFlagsList]
  | cons b bs ih =>
      cases b with
      | false =>
          simpa [relativeBoundaryFlagsList] using ih
      | true =>
          simpa [relativeBoundaryFlagsList] using
            BoolListAllTrue.cons_true ih

/-- one true->false difference は relative flags 上で exactly one false になる。 -/
theorem relativeBoundaryFlagsList_exactlyOneFalse
    {upper lower : List Bool}
    (h : OneTrueToFalse upper lower) :
    ExactlyOneFalse (relativeBoundaryFlagsList upper lower) := by
  induction h with
  | @here xs =>
      change ExactlyOneFalse
        (false :: relativeBoundaryFlagsList xs xs)
      exact ExactlyOneFalse.head
        (relativeBoundaryFlagsList_self_allTrue xs)
  | @there u xs ys h ih =>
      cases u with
      | false =>
          simpa [relativeBoundaryFlagsList] using ih
      | true =>
          change ExactlyOneFalse
            (true :: relativeBoundaryFlagsList xs ys)
          exact ExactlyOneFalse.tail ih

/--
`List.ofFn f` の先頭座標が `true` のとき、
その座標だけを `false` にすると `OneTrueToFalse`。

`List.ofFn` の先頭を展開すると、これは `OneTrueToFalse.here` そのものになる。
-/
private theorem oneTrueToFalse_ofFn_erase_zero
    {n : ℕ}
    (f : Fin (n + 1) → Bool)
    (h0 : f 0 = true) :
    OneTrueToFalse
      (List.ofFn f)
      (List.ofFn
        (fun i =>
          if i = (0 : Fin (n + 1)) then false else f i)) := by
  rw [List.ofFn_succ, List.ofFn_succ]
  simpa [h0] using
    (OneTrueToFalse.here
      (xs := List.ofFn (fun i : Fin n => f i.succ)))

/--
tail 上の `OneTrueToFalse` は、共通の先頭 Bool を付けても保持される。

従って `b'.succ` 座標だけを false にする問題は、
tail 上で `b'` 座標だけを false にする問題へ帰着する。
-/
private theorem oneTrueToFalse_ofFn_erase_succ
    {n : ℕ}
    (f : Fin (n + 1) → Bool)
    (b : Fin n)
    (hTail :
      OneTrueToFalse
        (List.ofFn (fun i : Fin n => f i.succ))
        (List.ofFn
          (fun i : Fin n =>
            if i = b then false else f i.succ))) :
    OneTrueToFalse
      (List.ofFn f)
      (List.ofFn
        (fun i =>
          if i = b.succ then false else f i)) := by
  rw [List.ofFn_succ, List.ofFn_succ]
  have hZero :
      (0 : Fin (n + 1)) ≠ b.succ := by
    intro hEq
    have hVal := congrArg Fin.val hEq
    simp at hVal
  have hTailEq :
      List.ofFn
          (fun i : Fin n =>
            if i.succ = b.succ then false else f i.succ) =
        List.ofFn
          (fun i : Fin n =>
            if i = b then false else f i.succ) := by
    congr 1
    funext i
    by_cases hi : i = b
    · subst i
      simp
    · have hSucc : i.succ ≠ b.succ := by
        intro hEq
        exact hi (Fin.succ_injective n hEq)
      simp [hi, hSucc]
  rw [ite_eq_right hZero, hTailEq]
  exact OneTrueToFalse.there hTail

/--
長さ `n` の `List.ofFn` について
「一つの `true` 座標だけを `false` にすると `OneTrueToFalse`」
が成立すると仮定する。

すると長さ `n + 1` についても同じ性質が成立する。

変更する座標が `0` なら `oneTrueToFalse_ofFn_erase_zero`、
`b'.succ` なら tail に帰納仮定を適用してから
`oneTrueToFalse_ofFn_erase_succ` で先頭を復元する。
-/
private theorem oneTrueToFalse_ofFn_erase_succ_length
    {n : ℕ}
    (f : Fin (n + 1) → Bool)
    (ih :
      ∀ (g : Fin n → Bool) (b : Fin n),
        g b = true →
        OneTrueToFalse
          (List.ofFn g)
          (List.ofFn
            (fun i =>
              if i = b then false else g i)))
    (b : Fin (n + 1))
    (hb : f b = true) :
    OneTrueToFalse
      (List.ofFn f)
      (List.ofFn
        (fun i =>
          if i = b then false else f i)) := by
  refine Fin.cases
    (motive := fun b : Fin (n + 1) =>
      f b = true →
      OneTrueToFalse
        (List.ofFn f)
        (List.ofFn
          (fun i =>
            if i = b then false else f i)))
    ?_ (fun b' => ?_) b hb
  · intro h0
    exact oneTrueToFalse_ofFn_erase_zero f h0
  · intro hb'
    let f' : Fin n → Bool :=
      fun i => f i.succ
    have hbTail : f' b' = true := by
      exact hb'
    have hIH :
        OneTrueToFalse
          (List.ofFn f')
          (List.ofFn
            (fun i =>
              if i = b' then false else f' i)) :=
      ih f' b' hbTail
    exact oneTrueToFalse_ofFn_erase_succ
      f b' hIH


/--
`List.ofFn f` の一つの `true` 座標だけを `false` にすると
`OneTrueToFalse` が成立する。

長さについて帰納法を行う。
空の `Fin 0` には座標が存在せず、
後続長の場合は `oneTrueToFalse_ofFn_erase_succ_length`
に帰着する。
-/
theorem oneTrueToFalse_ofFn_erase
    {n : ℕ}
    (f : Fin n → Bool)
    (b : Fin n)
    (hb : f b = true) :
    OneTrueToFalse
      (List.ofFn f)
      (List.ofFn
        (fun i =>
          if i = b then false else f i)) := by
  induction n with
  | zero =>
      exact Fin.elim0 b
  | succ n ih =>
      exact oneTrueToFalse_ofFn_erase_succ_length
        f ih b hb

/--
`retainedFlags` は `List.ofFn` そのものなので、
消去後 pattern の retained flags は
`List.ofFn (eraseRetainedBoundary R b)` に定義的に等しい。
-/
private theorem retainedFlags_eraseRetainedBoundary_eq
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    retainedFlags (eraseRetainedBoundary R b) =
      List.ofFn
        (eraseRetainedBoundary R b) := by
  rfl

/--
`b` が retained な内部境界なら、
`eraseRetainedBoundary R b` はその一点だけを
`true` から `false` へ変更する。
-/
private theorem eraseRetainedBoundary_oneTrueToFalse
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    OneTrueToFalse
      (List.ofFn R)
      (List.ofFn (eraseRetainedBoundary R b)) := by
  unfold eraseRetainedBoundary
  exact oneTrueToFalse_ofFn_erase R b hb

/--
retained flags では `eraseRetainedBoundary` が
exact に一つの true->false change。
-/
theorem retainedFlags_erase_oneTrueToFalse
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    OneTrueToFalse
      (retainedFlags R)
      (retainedFlags (eraseRetainedBoundary R b)) := by
  unfold retainedFlags
  exact eraseRetainedBoundary_oneTrueToFalse R b hb

/--
`eraseRetainedBoundary R b` を flags にすると、
座標 `b` だけを明示的に `false` にした `List.ofFn` と一致する。
-/
private theorem retainedFlags_eraseRetainedBoundary_eq_explicitErase
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    retainedFlags (eraseRetainedBoundary R b) =
      List.ofFn
        (fun i : InternalRecordBoundary D =>
          if i = b then false else R i) := by
  rw [retainedFlags_eraseRetainedBoundary_eq R b]
  rfl

/-- genuine one-boundary deletion の relative flags には false がちょうど一つ。 -/
theorem relativeBoundaryFlags_erase_exactlyOneFalse
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    ExactlyOneFalse
      (relativeBoundaryFlags R (eraseRetainedBoundary R b)) := by
  unfold relativeBoundaryFlags
  exact relativeBoundaryFlagsList_exactlyOneFalse
    (retainedFlags_erase_oneTrueToFalse R b hb)

/-! ## 2. RecordChain の local-area vector -/

/-- RecordChain length list に沿って source point から直接切り出した local-area vector。 -/
def recordChainLocalDecorationAreas
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ)
    (lengths : List ℕ) : List ℕ :=
  (RecordChain.blockWordsFromLengths x start lengths).map localDecorationArea

@[simp] theorem recordChainLocalDecorationAreas_nil
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ) :
    recordChainLocalDecorationAreas x start [] = [] := rfl

@[simp] theorem recordChainLocalDecorationAreas_cons
    {p H : ℕ}
    (x : FiberPoint p H)
    (start len : ℕ)
    (rest : List ℕ) :
    recordChainLocalDecorationAreas x start (len :: rest) =
      localDecorationArea (blockWord x start len) ::
        recordChainLocalDecorationAreas x (start + len) rest := rfl

/-- decomposition の local-area vector は chain から直接切った vector と同じ。 -/
theorem recordDecomposition_localDecorationAreas_eq_chain
    {p H : ℕ}
    {x : FiberPoint p H}
    (D : RecordDecomposition x 1) :
    localDecorationAreas D =
      recordChainLocalDecorationAreas x 1 D.lengths := by
  rfl

/-- compact-support replacement の完全な右側にある chain の local areas は全て保存。 -/
theorem BlockReplacement.recordChainLocalDecorationAreas_eq_of_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hRight : c ≤ start) :
    recordChainLocalDecorationAreas u start lengths =
      recordChainLocalDecorationAreas v start lengths := by
  induction C with
  | @last start len B hTerminal =>
      change
        localDecorationArea (blockWord u start len) :: [] =
          localDecorationArea (blockWord v start len) :: []
      have hArea := R.localDecorationArea_blockWord_eq_of_right
        hRight (by omega : start + len ≤ p)
      rw [hArea]
  | @cons start len rest B hInterior T ih =>
      change
        localDecorationArea (blockWord u start len) ::
            recordChainLocalDecorationAreas u (start + len) rest =
          localDecorationArea (blockWord v start len) ::
            recordChainLocalDecorationAreas v (start + len) rest
      have hArea := R.localDecorationArea_blockWord_eq_of_right
        hRight (Nat.le_of_lt hInterior)
      rw [hArea]
      exact congrArg (List.cons _) (ih (by omega))

/-! ## 3. adjacent pair を P27 flat target で直接 merge -/

/--
P27 flat target を使った interior adjacent pair の choice-free direct merge data。
-/
structure FlatInteriorAdjacentMergeResult
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (a r s : ℕ)
    (A : AdjacentInteriorRecordPair P u a r s) where
  point : FiberPoint P.oddCount P.twoDepth
  point_eq_flat :
    point = flatIntervalTarget u a ((a + r) + s)
      (by
        have hr := A.leftSource.length_pos
        have hs := A.rightSource.length_pos
        omega)
      (Nat.le_of_lt A.outerInterior)
      A.anchorRoof
      (Or.inr A.outerRoof)
  replacement : BlockReplacement u point a ((a + r) + s)
  firstCrossing : FirstCrossing point.word
  mergedBlock : RecordBlock point a (r + s)
  mergedAreaZero :
    localDecorationArea (blockWord point a (r + s)) = 0

/-- interior adjacent pair の direct flat merge。 -/
noncomputable def flatInteriorAdjacentMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    FlatInteriorAdjacentMergeResult P u a r s A := by
  let c := (a + r) + s
  have hac : a < c := by
    have hr := A.leftSource.length_pos
    have hs := A.rightSource.length_pos
    omega
  have hcp : c ≤ P.oddCount := Nat.le_of_lt A.outerInterior
  have hRoofA : RoofContact u a := A.anchorRoof
  have hRoofC : RoofContact u c := by
    simpa [c] using A.outerRoof
  let v : FiberPoint P.oddCount P.twoDepth :=
    flatIntervalTarget u a c hac hcp hRoofA (Or.inr hRoofC)
  have hRep : BlockReplacement u v a c := by
    dsimp [v]
    exact flatIntervalTarget_blockReplacement
      u a c hac hcp hRoofA (Or.inr hRoofC)
  have hFv : FirstCrossing v.word := by
    dsimp [v]
    exact flatIntervalTarget_firstCrossing
      u a c hac hcp hRoofA (Or.inr hRoofC) hFu
  have hRoofStart : RoofContact v a := by
    dsimp [v]
    exact flatIntervalTarget_leftRoof
      u a c hac hcp hRoofA (Or.inr hRoofC)
  have hRoofStop : RoofContact v c := by
    dsimp [v]
    exact flatIntervalTarget_rightRoof
      u a c hac hcp hRoofA hRoofC A.outerInterior
  let Rrun : InteriorRecordRun u a [r, s] c :=
    InteriorRecordRun.cons A.leftSource A.leftInterior
      (InteriorRecordRun.one A.rightSource A.outerInterior)
  have hCarry : criticalCarry a (r + s) = 1 := by
    have h := Rrun.outerCarry_one
    simpa [c] using h
  have hEnd : a + (r + s) = c := by
    dsimp [c]
    omega
  have hHeight := height_add_eq_add_blockDepth v a (r + s)
  have hCrit := criticalHeight_add_eq a (r + s)
  unfold RoofContact at hRoofStart hRoofStop
  rw [hEnd, hRoofStart, hRoofStop] at hHeight
  rw [hCarry] at hCrit
  have hCritStop :
      criticalHeight c =
        criticalHeight a + (criticalHeight (r + s) + 1) := by
    rw [← hEnd]
    simpa [Nat.add_assoc] using hCrit
  have hTotal :
      twoSteps (blockWord v a (r + s)) =
        criticalHeight (r + s) + 1 := by
    have hEq :
        criticalHeight a + twoSteps (blockWord v a (r + s)) =
          criticalHeight a + (criticalHeight (r + s) + 1) :=
      hHeight.symm.trans hCritStop
    exact Nat.add_left_cancel hEq
  have hLenPos : 0 < r + s := by
    have hr := A.leftSource.length_pos
    omega
  have hMinimal : MinimalBlock (blockWord v a (r + s)) := by
    dsimp [v]
    exact flatIntervalTarget_minimalBlock_of_totalDepth
      u a c (r + s) hac hcp hRoofA (Or.inr hRoofC)
      hEnd hLenPos hTotal
  have hLenLt : r + s < P.oddCount := by
    have ha := A.anchor_pos
    omega
  have hDrop := chordDrop_of_primitiveReduced
    P hPrimitive hReduced hLenPos hLenLt
  have hMerged : RecordBlock v a (r + s) := by
    apply RecordBlock.ofMinimalAtRoof
      v hLenPos (by omega) hMinimal hRoofStart
    · intro j hjPos _hjLt
      exact P.criticalHeight_below_chord hjPos
    · exact hDrop
    · intro _hInterior
      rw [hEnd]
      exact hRoofStop
  have hArea :
      localDecorationArea (blockWord v a (r + s)) = 0 := by
    dsimp [v]
    exact flatIntervalTarget_mergedLocalDecorationArea_eq_zero
      u a c (r + s) hac hcp hRoofA (Or.inr hRoofC) hEnd
  exact {
    point := v
    point_eq_flat := rfl
    replacement := hRep
    firstCrossing := hFv
    mergedBlock := hMerged
    mergedAreaZero := hArea
  }

/-- terminal adjacent pair の P27 flat direct merge data。 -/
structure FlatTerminalAdjacentMergeResult
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (a r s : ℕ)
    (T : AdjacentTerminalRecordPair P u a r s) where
  point : FiberPoint P.oddCount P.twoDepth
  point_eq_flat :
    point = flatIntervalTarget u a P.oddCount
      T.anchor_lt_terminal le_rfl T.anchorRoof (Or.inl rfl)
  replacement : BlockReplacement u point a P.oddCount
  firstCrossing : FirstCrossing point.word
  mergedBlock : RecordBlock point a (r + s)
  mergedAreaZero :
    localDecorationArea (blockWord point a (r + s)) = 0

/-- terminal adjacent pair の direct flat merge。 -/
noncomputable def flatTerminalAdjacentMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    FlatTerminalAdjacentMergeResult P u a r s T := by
  have hStartLt : a < P.oddCount := T.anchor_lt_terminal
  have hRoofA : RoofContact u a := T.anchorRoof
  let v : FiberPoint P.oddCount P.twoDepth :=
    flatIntervalTarget u a P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl)
  have hRep : BlockReplacement u v a P.oddCount := by
    dsimp [v]
    exact flatIntervalTarget_blockReplacement
      u a P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl)
  have hFv : FirstCrossing v.word := by
    dsimp [v]
    exact flatIntervalTarget_firstCrossing
      u a P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl) hFu
  have hRoofStart : RoofContact v a := by
    dsimp [v]
    exact flatIntervalTarget_leftRoof
      u a P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl)
  have hEnd : a + (r + s) = P.oddCount :=
    T.anchor_add_outerLength_eq_terminal
  have hComplement :=
    criticalHeight_add_complement_add_one_eq_twoDepth_of_primitiveReduced
      P hPrimitive hReduced T.anchor_pos hStartLt
  have hLenEq : r + s = P.oddCount - a := by omega
  rw [← hLenEq] at hComplement
  have hHeight := height_add_eq_add_blockDepth v a (r + s)
  unfold RoofContact at hRoofStart
  rw [hEnd, v.height_terminal, hRoofStart] at hHeight
  have hTotal :
      twoSteps (blockWord v a (r + s)) =
        criticalHeight (r + s) + 1 := by
    omega
  have hLenPos : 0 < r + s := by
    have hr := T.leftSource.length_pos
    omega
  have hMinimal : MinimalBlock (blockWord v a (r + s)) := by
    dsimp [v]
    exact flatIntervalTarget_minimalBlock_of_totalDepth
      u a P.oddCount (r + s) hStartLt le_rfl hRoofA (Or.inl rfl)
      hEnd hLenPos hTotal
  have hLenLt : r + s < P.oddCount := by
    have hAnchorPos : 0 < a := T.anchor_pos
    omega
  have hDrop := chordDrop_of_primitiveReduced
    P hPrimitive hReduced hLenPos hLenLt
  have hMerged : RecordBlock v a (r + s) := by
    apply RecordBlock.ofMinimalAtRoof
      v hLenPos (by omega) hMinimal hRoofStart
    · intro j hjPos _hjLt
      exact P.criticalHeight_below_chord hjPos
    · exact hDrop
    · intro hInterior
      rw [hEnd] at hInterior
      omega
  have hArea :
      localDecorationArea (blockWord v a (r + s)) = 0 := by
    dsimp [v]
    exact flatIntervalTarget_mergedLocalDecorationArea_eq_zero
      u a P.oddCount (r + s) hStartLt le_rfl hRoofA (Or.inl rfl) hEnd
  exact {
    point := v
    point_eq_flat := rfl
    replacement := hRep
    firstCrossing := hFv
    mergedBlock := hMerged
    mergedAreaZero := hArea
  }

/-! ## 4. exactly-one-false actual coarsening は一つの compact-support merge -/

/--
先頭 flag が `true` の場合、tail で得られた local-area formula に
保存された先頭 RecordBlock の area を付け戻せる。
-/
private theorem recordChainLocalDecorationAreas_cons_true_of_tail
    {p H a c start len : ℕ}
    {u v : FiberPoint p H}
    {rest outTail : List ℕ}
    {more : List Bool}
    (hRestNe : rest ≠ [])
    (hRep : BlockReplacement u v a c)
    (hLeft : start + len ≤ a)
    (hAreas :
      recordChainLocalDecorationAreas
          v (start + len) outTail =
        LocalAreaTuple.canonicalCoarsenValues
          (recordChainLocalDecorationAreas
            u (start + len) rest)
          more) :
    recordChainLocalDecorationAreas
        v start (len :: outTail) =
      LocalAreaTuple.canonicalCoarsenValues
        (recordChainLocalDecorationAreas
          u start (len :: rest))
        (true :: more) := by
  cases rest with
  | nil =>
      exact (hRestNe rfl).elim
  | cons len2 rest2 =>
      have hAreas' :
          recordChainLocalDecorationAreas
              v (start + len) outTail =
            LocalAreaTuple.canonicalCoarsenValues
              (localDecorationArea
                  (blockWord u (start + len) len2) ::
                recordChainLocalDecorationAreas
                  u ((start + len) + len2) rest2)
              more := by
        simpa only [recordChainLocalDecorationAreas_cons] using hAreas
      simp only [
        recordChainLocalDecorationAreas_cons,
        LocalAreaTuple.canonicalCoarsenValues_true
      ]
      have hHeadArea :=
        hRep.localDecorationArea_blockWord_eq_of_left hLeft
      rw [hHeadArea]
      exact congrArg
        (List.cons
          (localDecorationArea (blockWord v start len)))
        hAreas'


/--
terminal adjacent merge の merged block は、
それだけで terminal RecordChain を作る。
-/
private theorem flatTerminalAdjacentMergeResult_recordChain
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    {T : AdjacentTerminalRecordPair P u a r s}
    (M : FlatTerminalAdjacentMergeResult P u a r s T) :
    RecordChain M.point a [r + s] := by
  exact RecordChain.last
    M.mergedBlock
    T.anchor_add_outerLength_eq_terminal


/--
terminal flat merge の replacement endpoint を、
source の隣接二 block の右端 `(a + r) + s` として読み直す。
-/
private theorem flatTerminalAdjacentMergeResult_replacement_outer
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    {T : AdjacentTerminalRecordPair P u a r s}
    (M : FlatTerminalAdjacentMergeResult P u a r s T) :
    BlockReplacement u M.point a ((a + r) + s) := by
  have hStop : (a + r) + s = P.oddCount := by
    have hEnd := T.anchor_add_outerLength_eq_terminal
    omega
  rw [hStop]
  exact M.replacement


/--
terminal adjacent merge では、二つの source block に対する
`false` coarsening の local-area vector が
merged target の singleton local-area vector と一致する。
-/
private theorem flatTerminalAdjacentMergeResult_area_formula
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    {T : AdjacentTerminalRecordPair P u a r s}
    (M : FlatTerminalAdjacentMergeResult P u a r s T) :
    recordChainLocalDecorationAreas
        M.point a [r + s] =
      LocalAreaTuple.canonicalCoarsenValues
        (recordChainLocalDecorationAreas
          u a [r, s])
        [false] := by
  simp only [
    recordChainLocalDecorationAreas_cons,
    recordChainLocalDecorationAreas_nil,
    LocalAreaTuple.canonicalCoarsenValues_false,
    LocalAreaTuple.canonicalCoarsenValues,
    LocalAreaTuple.flattenHeadAreaValues,
    M.mergedAreaZero
  ]


/--
interior adjacent merge の右側 tail は replacement の外側なので保存される。
従って merged block と保存された tail を連結して
新しい RecordChain を作れる。
-/
private theorem flatInteriorAdjacentMergeResult_recordChain
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    {A : AdjacentInteriorRecordPair P u a r s}
    (M : FlatInteriorAdjacentMergeResult P u a r s A)
    {rest : List ℕ}
    (Ttail : RecordChain u ((a + r) + s) rest) :
    RecordChain M.point a ((r + s) :: rest) := by
  have hTailSaved :
      RecordChain M.point ((a + r) + s) rest := by
    exact Ttail.preserved_on_right M.replacement le_rfl
  have hMergedInterior :
      a + (r + s) < P.oddCount := by
    have hOuter := A.outerInterior
    omega
  have hTail :
      RecordChain M.point (a + (r + s)) rest := by
    simpa [Nat.add_assoc] using hTailSaved
  exact RecordChain.cons
    M.mergedBlock
    hMergedInterior
    hTail


/--
interior adjacent merge では merged block の local area は 0 になり、
replacement の完全な右側の local areas は保存される。

後続 flags がすべて `true` なら、その二つを合わせた target vector は
source vector の `false :: more` canonical coarsening と一致する。
-/
private theorem flatInteriorAdjacentMergeResult_area_formula
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    {A : AdjacentInteriorRecordPair P u a r s}
    (M : FlatInteriorAdjacentMergeResult P u a r s A)
    {rest : List ℕ}
    (Ttail : RecordChain u ((a + r) + s) rest)
    (more : List Bool)
    (hAllTrue : BoolListAllTrue more) :
    recordChainLocalDecorationAreas
        M.point a ((r + s) :: rest) =
      LocalAreaTuple.canonicalCoarsenValues
        (recordChainLocalDecorationAreas
          u a (r :: s :: rest))
        (false :: more) := by
  have hRightAreas :=
    M.replacement.recordChainLocalDecorationAreas_eq_of_right
      Ttail le_rfl
  have hTailAreaIdentity :=
    LocalAreaTuple.canonicalCoarsenValues_eq_self_of_allTrue
      (recordChainLocalDecorationAreas
        u (a + r) (s :: rest))
      more
      hAllTrue
  have hTailAreaIdentity' :
      LocalAreaTuple.canonicalCoarsenValues
          (localDecorationArea
              (blockWord u (a + r) s) ::
            recordChainLocalDecorationAreas
              u ((a + r) + s) rest)
          more =
        localDecorationArea
            (blockWord u (a + r) s) ::
          recordChainLocalDecorationAreas
            u ((a + r) + s) rest := by
    simpa only [recordChainLocalDecorationAreas_cons]
      using hTailAreaIdentity
  simp only [recordChainLocalDecorationAreas_cons]
  rw [M.mergedAreaZero]
  rw [LocalAreaTuple.canonicalCoarsenValues_false]
  rw [hTailAreaIdentity']
  simp only [LocalAreaTuple.flattenHeadAreaValues]
  simpa [Nat.add_assoc] using
    congrArg (List.cons 0) hRightAreas.symm

/--
Exactly-one-false flags に対する actual coarsening の強化版。

P29 の existence theorem と違い、support interval と source adjacent pair、
target merged block、local-area vector formula を同時に保持する。
-/
theorem RecordChain.exists_compactCoarsening_of_exactlyOneFalse
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {u : FiberPoint P.oddCount P.twoDepth}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hFu : FirstCrossing u.word)
    (flags : List Bool)
    (hFlags : flags.length = lengths.length - 1)
    (hOne : ExactlyOneFalse flags)
    (hStartPos : 0 < start) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ out : List ℕ,
        ∃ _Cv : RecordChain v start out,
          ∃ a r s : ℕ,
            FirstCrossing v.word ∧
            out = coarsenByFlags lengths flags ∧
            start ≤ a ∧
            RecordBlock u a r ∧
            RecordBlock u (a + r) s ∧
            BlockReplacement u v a ((a + r) + s) ∧
            RecordBlock v a (r + s) ∧
            localDecorationArea (blockWord v a (r + s)) = 0 ∧
            recordChainLocalDecorationAreas v start out =
              LocalAreaTuple.canonicalCoarsenValues
                (recordChainLocalDecorationAreas u start lengths) flags := by
  induction C generalizing flags with
  | @last start len B hTerminal =>
      have hFlags0 : flags.length = 0 := by
        simpa using hFlags
      have hNil : flags = [] :=
        List.eq_nil_of_length_eq_zero hFlags0
      subst flags
      exact (hOne.ne_nil rfl).elim
  | @cons start len rest B hInterior T ih =>
      have hRestNe : rest ≠ [] := T.nonempty
      cases flags with
      | nil =>
          exact (hOne.ne_nil rfl).elim
      | cons keep more =>
          have hMore :
              more.length = rest.length - 1 := by
            have hRestLenPos : 0 < rest.length :=
              List.length_pos_iff.mpr hRestNe
            simp only [List.length_cons] at hFlags
            omega
          cases keep with
          | true =>
              cases hOne with
              | tail hOneMore =>
                  obtain ⟨v, outTail, Ctail, a, r, s,
                    hFv, hOutTail, hStartA,
                    hLeft, hRight, hRep,
                    hMerged, hAreaZero, hAreas⟩ :=
                    ih more hMore hOneMore (by omega)
                  have hBv :
                      RecordBlock v start len := by
                    exact B.preserved_on_left hRep hStartA
                  let Cwhole :
                      RecordChain v start (len :: outTail) :=
                    RecordChain.cons hBv hInterior Ctail
                  refine
                    ⟨v, len :: outTail, Cwhole,
                      a, r, s,
                      hFv, ?_, ?_,
                      hLeft, hRight, hRep,
                      hMerged, hAreaZero, ?_⟩
                  · rw [coarsenByFlags_cons_true
                      len hRestNe more]
                    rw [← hOutTail]
                  · omega
                  · exact
                      recordChainLocalDecorationAreas_cons_true_of_tail
                        hRestNe
                        hRep
                        hStartA
                        hAreas
          | false =>
              cases hOne with
              | head hAllTrue =>
                  cases T with
                  | @last _ len2 B2 hTerminal2 =>
                      let pair :
                          AdjacentTerminalRecordPair
                            P u start len len2 := {
                        anchor_pos := hStartPos
                        leftSource := B
                        rightSource := B2
                        outerTerminal := hTerminal2
                      }
                      let M :=
                        flatTerminalAdjacentMerge
                          P hPrimitive hReduced
                          u hFu pair
                      let Cv :
                          RecordChain
                            M.point start [len + len2] :=
                        flatTerminalAdjacentMergeResult_recordChain
                          M
                      have hMoreNil : more = [] := by
                        apply List.eq_nil_of_length_eq_zero
                        simpa using hMore
                      subst more
                      refine
                        ⟨M.point, [len + len2], Cv,
                          start, len, len2,
                          M.firstCrossing,
                          ?_, le_rfl,
                          B, B2,
                          ?_,
                          M.mergedBlock,
                          M.mergedAreaZero,
                          ?_⟩
                      · simp [
                          coarsenByFlags,
                          mergeHeadLength
                        ]
                      · exact
                          flatTerminalAdjacentMergeResult_replacement_outer
                            M
                      · exact
                          flatTerminalAdjacentMergeResult_area_formula
                            M
                  | @cons _ len2 rest2 B2 hInterior2 T2 =>
                      let pair :
                          AdjacentInteriorRecordPair
                            P u start len len2 := {
                        anchor_pos := hStartPos
                        leftSource := B
                        rightSource := B2
                        outerInterior := hInterior2
                      }
                      let M :=
                        flatInteriorAdjacentMerge
                          P hPrimitive hReduced
                          u hFu pair
                      let Cv :
                          RecordChain
                            M.point
                            start
                            ((len + len2) :: rest2) :=
                        flatInteriorAdjacentMergeResult_recordChain
                          M T2
                      have hTailLengths :
                          coarsenByFlags
                              (len2 :: rest2) more =
                            len2 :: rest2 :=
                        coarsenByFlags_eq_self_of_allTrue
                          (len2 :: rest2)
                          more
                          hAllTrue
                      refine
                        ⟨M.point,
                          (len + len2) :: rest2,
                          Cv,
                          start, len, len2,
                          M.firstCrossing,
                          ?_, le_rfl,
                          B, B2,
                          ?_,
                          M.mergedBlock,
                          M.mergedAreaZero,
                          ?_⟩
                      · rw [
                          coarsenByFlags_cons_false
                            len hRestNe more
                        ]
                        rw [hTailLengths]
                        rfl
                      · exact M.replacement
                      · exact
                          flatInteriorAdjacentMergeResult_area_formula
                            M T2 more hAllTrue



/-! ## 5. BoundaryDecorationActualFiber coordinate は任意 decomposition の local areas と一致 -/

/--
actual boundary fiber point の area-product coordinate values は、同じ point の任意の
cut-1 RecordDecomposition から読む `localDecorationAreas` と exact に一致する。
-/
theorem boundaryDecorationFiberEquiv_values_eq_localDecorationAreas_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R)
    (E : RecordDecomposition X.1 1) :
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R X).values =
      localDecorationAreas E := by
  change
    (LocalAreaTuple.cast
      (boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D R)
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (boundaryCanonicalDecomposition
          P hPrimitive hReduced u D R)
        X)).values =
      localDecorationAreas E
  rw [LocalAreaTuple.cast_values]
  have hFixed :=
    fixedSkeletonLocalAreaTuple_eq
      P hPrimitive hReduced
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (boundaryCanonicalDecomposition
        P hPrimitive hReduced u D R)
      X
  have hFixedValues :=
    congrArg LocalAreaTuple.values hFixed
  rw [hFixedValues]
  rw [LocalDecorationTuple.toLocalAreaTuple_values]
  rw [X.toLocalDecorationTuple_blocks_eq_any_decomposition E]
  rfl

/-! ## 6. 主定理: canonical one-boundary merge 自身が compact support -/

/--
## Canonical One-Boundary Merge Compact Support

保持されている境界 `b` を一つ消す canonical actual merge は、source のある隣接二
RecordBlock `[r,s]` の外端 `(a,(a+r)+s)` だけを support に持つ actual `BlockReplacement`。

さらに target ではその二 block が一つの genuine `RecordBlock (r+s)` になり、
merged local decoration area は exact に 0。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_compactSupport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    ∃ a r s : ℕ,
      RecordBlock X.1 a r ∧
      RecordBlock X.1 (a + r) s ∧
      BlockReplacement
        X.1
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X).1
        a ((a + r) + s) ∧
      RecordBlock
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X).1
        a (r + s) ∧
      localDecorationArea
        (blockWord
          (boundaryDecorationActualCanonicalInterfiberMerge
            P hPrimitive hReduced u D R b X).1
          a (r + s)) = 0 := by
  let q := relativeBoundaryFlags R (eraseRetainedBoundary R b)
  have hQOne : ExactlyOneFalse q := by
    dsimp [q]
    exact relativeBoundaryFlags_erase_exactlyOneFalse R b hb
  have hXLengths :
      X.decomposition.lengths = coarsenedLengthsFor D R :=
    boundaryDecorationActualFiber_decomposition_lengths
      P hPrimitive hReduced u D R X
  have hQLen : q.length = X.decomposition.lengths.length - 1 := by
    dsimp [q]
    rw [hXLengths]
    exact relativeBoundaryFlags_erase_length D R b
  obtain ⟨v, out, Cv, a, r, s,
    hFv, hOut, hStartA,
    hLeft, hRight, hRep, hMerged, hAreaZero, hAreas⟩ :=
    X.decomposition.chain.exists_compactCoarsening_of_exactlyOneFalse
      P hPrimitive hReduced
      X.decomposition.whole_firstCrossing
      q hQLen hQOne (by omega)
  let E : RecordDecomposition v 1 := {
    lengths := out
    chain := Cv
    whole_firstCrossing := hFv
  }
  have hOutTarget : out = coarsenedLengthsFor D (eraseRetainedBoundary R b) := by
    calc
      out = coarsenByFlags X.decomposition.lengths q := hOut
      _ = coarsenByFlags (coarsenedLengthsFor D R) q := by rw [hXLengths]
      _ = coarsenedLengthsFor D (eraseRetainedBoundary R b) := by
        dsimp [q]
        exact coarsenByFlags_relativeBoundaryFlags_erase D R b
  let Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D (eraseRetainedBoundary R b) := by
    refine ⟨v, ?_⟩
    refine ⟨E, ?_⟩
    exact hOutTarget.trans
      (boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)).symm
  have hYValues :
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) Y).values =
        recordChainLocalDecorationAreas v 1 out := by
    calc
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) Y).values =
        localDecorationAreas E :=
          boundaryDecorationFiberEquiv_values_eq_localDecorationAreas_of_decomposition
            P hPrimitive hReduced u D
            (eraseRetainedBoundary R b) Y E
      _ = recordChainLocalDecorationAreas v 1 out := by
        rfl
  have hXValues :
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X).values =
        recordChainLocalDecorationAreas X.1 1 X.decomposition.lengths := by
    calc
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X).values =
        localDecorationAreas X.decomposition :=
          boundaryDecorationFiberEquiv_values_eq_localDecorationAreas_of_decomposition
            P hPrimitive hReduced u D R X X.decomposition
      _ = recordChainLocalDecorationAreas X.1 1 X.decomposition.lengths := by
        rfl
  have hValues :
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) Y).values =
        LocalAreaTuple.canonicalCoarsenValues
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).values
          (relativeBoundaryFlags R (eraseRetainedBoundary R b)) := by
    rw [hYValues, hXValues]
    simpa [q] using hAreas
  have hEq :
      Y = boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b X :=
    boundaryDecorationActualCanonicalInterfiberMerge_eq_of_values
      P hPrimitive hReduced u D R b X Y hValues
  refine ⟨a, r, s, hLeft, hRight, ?_, ?_, ?_⟩
  · have hRep' : BlockReplacement X.1 Y.1 a ((a + r) + s) := by
      simpa [Y] using hRep
    rw [← hEq]
    exact hRep'
  · have hMerged' : RecordBlock Y.1 a (r + s) := by
      simpa [Y] using hMerged
    rw [← hEq]
    exact hMerged'
  · have hArea' : localDecorationArea (blockWord Y.1 a (r + s)) = 0 := by
      simpa [Y] using hAreaZero
    rw [← hEq]
    exact hArea'

/-- 主定理から compact support だけを取り出した短い API。 -/
theorem boundaryDecorationActualCanonicalInterfiberMerge_blockReplacement
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    ∃ a c : ℕ,
      BlockReplacement
        X.1
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X).1
        a c := by
  obtain ⟨a, r, s, _hL, _hR, hRep, _hM, _hA⟩ :=
    boundaryDecorationActualCanonicalInterfiberMerge_compactSupport
      P hPrimitive hReduced u D R b hb X
  exact ⟨a, (a + r) + s, hRep⟩

/--
canonical merge で消える local factor は genuine flat factor: merged area は 0。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_mergedArea_zero
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    ∃ a r s : ℕ,
      RecordBlock X.1 a r ∧
      RecordBlock X.1 (a + r) s ∧
      RecordBlock
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X).1
        a (r + s) ∧
      localDecorationArea
        (blockWord
          (boundaryDecorationActualCanonicalInterfiberMerge
            P hPrimitive hReduced u D R b X).1
          a (r + s)) = 0 := by
  obtain ⟨a, r, s, hL, hR, _hRep, hMerged, hArea⟩ :=
    boundaryDecorationActualCanonicalInterfiberMerge_compactSupport
      P hPrimitive hReduced u D R b hb X
  exact ⟨a, r, s, hL, hR, hMerged, hArea⟩

/-! ## 7. closure package -/

/--
canonical one-boundary merge compact-support 層で閉じた内容。
-/
structure BoundaryDecorationCanonicalMergeCompactSupportClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  genuine_merge_compact :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D)
      (X : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      R b = true →
      ∃ a r s : ℕ,
        RecordBlock X.1 a r ∧
        RecordBlock X.1 (a + r) s ∧
        BlockReplacement
          X.1
          (boundaryDecorationActualCanonicalInterfiberMerge
            P hPrimitive hReduced u D R b X).1
          a ((a + r) + s) ∧
        RecordBlock
          (boundaryDecorationActualCanonicalInterfiberMerge
            P hPrimitive hReduced u D R b X).1
          a (r + s) ∧
        localDecorationArea
          (blockWord
            (boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b X).1
            a (r + s)) = 0

/--
Canonical merge compact-support closure theorem。
-/
theorem boundaryDecorationCanonicalMergeCompactSupport_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationCanonicalMergeCompactSupportClosed
      P hPrimitive hReduced u D := by
  refine {
    genuine_merge_compact := ?_
  }
  intro R b X hb
  exact boundaryDecorationActualCanonicalInterfiberMerge_compactSupport
    P hPrimitive hReduced u D R b hb X

end RecordFerrers
end Collatz2
