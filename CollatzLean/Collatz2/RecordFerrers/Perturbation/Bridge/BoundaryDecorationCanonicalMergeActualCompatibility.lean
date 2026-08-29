import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationInterfiberMergeCoherence
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P28CanonicalCoarseningNormalization

/-!
# Record–Ferrers Perturbation / Canonical Merge Actual Compatibility

`BoundaryDecorationCanonicalInterfiberMerge` では、Boolean boundary order と
local-area product だけから canonical inter-fiber map を直接定義し、
`BoundaryDecorationInterfiberMergeCoherence` では identity / composition を閉じた。

一方 P27--P28 の actual geometry では、連続 Record 区間を `flatIntervalTarget` によって
左端 roof まで平坦化し、区間外を exact に保存する compact-support merge が既にある。

本ファイルでは両者を同じ local-area coordinate で比較する。

* `BlockReplacement` の完全な左側 / 右側にある local block の
  `localDecorationArea` は exact に不変。
* P27 `flatIntervalTarget` の merged interval は local area 0、すなわち
  canonical merge の `flatAreaValue` と同じ局所 datum を持つ。
* target fiber の area vector が canonical evaluator と一致する actual target は一意であり、
  canonical actual inter-fiber target そのものに一致する。
* 従って P27/P28 compact-support construction から得た target について
  「外側 area 保存 + merged area 0」を vector level まで読めば、
  その target と canonical target の equality が自動的に従う。
* flat section 上では canonical merge は canonical flat point の boundary deletion と
  exact に一致し、P34 の actual `BlockReplacement` geometry へ戻る。

このファイルの役割は、choice-free canonical coordinate dynamics と
P27--P28 compact-support actual geometry の間に lossless な comparison port を置くことである。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. BlockReplacement 外側では local area が不変 -/

namespace BlockReplacement

/--
replacement interval の完全な左側にある block では、
block 内の全 prefix depth が source / target で一致する。
-/
theorem prefixTwoDepth_blockWord_eq_of_left
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len k : ℕ}
    (hEnd : start + len ≤ a)
    (hk : k < len) :
    prefixTwoDepth (blockWord u start len) k =
      prefixTwoDepth (blockWord v start len) k := by
  have hEndP : start + len ≤ p := by
    have hac : a < c := R.start_lt_stop
    have hcp : c ≤ p := R.stop_le_terminal
    omega
  have hStartP : start ≤ p := by omega
  have hKP : start + k ≤ p := by omega
  have hStartA : start ≤ a := by omega
  have hKA : start + k ≤ a := by omega
  have hStartDisp := R.outside start hStartP (Or.inl hStartA)
  have hKDisp := R.outside (start + k) hKP (Or.inl hKA)
  have hStartHeight : u.height start = v.height start := by
    unfold profileDisplacement at hStartDisp
    exact_mod_cast (sub_eq_zero.mp hStartDisp).symm
  have hKHeight : u.height (start + k) = v.height (start + k) := by
    unfold profileDisplacement at hKDisp
    exact_mod_cast (sub_eq_zero.mp hKDisp).symm
  have hU := height_add_eq_add_blockDepth u start k
  have hV := height_add_eq_add_blockDepth v start k
  have hDepth :
      twoSteps (blockWord u start k) =
        twoSteps (blockWord v start k) := by
    omega
  unfold prefixTwoDepth
  have hTakeU :
      (blockWord u start len).take k = blockWord u start k := by
    simp [blockWord, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  have hTakeV :
      (blockWord v start len).take k = blockWord v start k := by
    simp [blockWord, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hTakeU, hTakeV, hDepth]

/--
replacement interval の完全な右側にある block でも、
block 内の全 prefix depth が source / target で一致する。
-/
theorem prefixTwoDepth_blockWord_eq_of_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len k : ℕ}
    (hRight : c ≤ start)
    (hEnd : start + len ≤ p)
    (hk : k < len) :
    prefixTwoDepth (blockWord u start len) k =
      prefixTwoDepth (blockWord v start len) k := by
  have hStartP : start ≤ p := by omega
  have hKP : start + k ≤ p := by omega
  have hStartDisp := R.outside start hStartP (Or.inr hRight)
  have hKDisp := R.outside (start + k) hKP (Or.inr (by omega))
  have hStartHeight : u.height start = v.height start := by
    unfold profileDisplacement at hStartDisp
    exact_mod_cast (sub_eq_zero.mp hStartDisp).symm
  have hKHeight : u.height (start + k) = v.height (start + k) := by
    unfold profileDisplacement at hKDisp
    exact_mod_cast (sub_eq_zero.mp hKDisp).symm
  have hU := height_add_eq_add_blockDepth u start k
  have hV := height_add_eq_add_blockDepth v start k
  have hDepth :
      twoSteps (blockWord u start k) =
        twoSteps (blockWord v start k) := by
    omega
  unfold prefixTwoDepth
  have hTakeU :
      (blockWord u start len).take k = blockWord u start k := by
    simp [blockWord, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  have hTakeV :
      (blockWord v start len).take k = blockWord v start k := by
    simp [blockWord, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hTakeU, hTakeV, hDepth]

/--
replacement interval の完全な左側では local block の `affineConst` が exact に不変。
-/
theorem affineConst_blockWord_eq_of_left
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len : ℕ}
    (hEnd : start + len ≤ a) :
    affineConst (blockWord u start len) =
      affineConst (blockWord v start len) := by
  have hEndP : start + len ≤ p := by
    have hac := R.start_lt_stop
    have hcp := R.stop_le_terminal
    omega
  have hOddU : oddSteps (blockWord u start len) = len :=
    oddSteps_blockWord u hEndP
  have hOddV : oddSteps (blockWord v start len) = len :=
    oddSteps_blockWord v hEndP
  rw [← affinePathSum_eq_affineConst, ← affinePathSum_eq_affineConst]
  unfold affinePathSum
  rw [hOddU, hOddV]
  apply Finset.sum_congr rfl
  intro k hkMem
  have hk : k < len := Finset.mem_range.mp hkMem
  unfold affinePathTerm
  rw [R.prefixTwoDepth_blockWord_eq_of_left hEnd hk]
  simp
  omega

/--
replacement interval の完全な右側でも local block の `affineConst` が exact に不変。
-/
theorem affineConst_blockWord_eq_of_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len : ℕ}
    (hRight : c ≤ start)
    (hEnd : start + len ≤ p) :
    affineConst (blockWord u start len) =
      affineConst (blockWord v start len) := by
  have hOddU : oddSteps (blockWord u start len) = len :=
    oddSteps_blockWord u hEnd
  have hOddV : oddSteps (blockWord v start len) = len :=
    oddSteps_blockWord v hEnd
  rw [← affinePathSum_eq_affineConst, ← affinePathSum_eq_affineConst]
  unfold affinePathSum
  rw [hOddU, hOddV]
  apply Finset.sum_congr rfl
  intro k hkMem
  have hk : k < len := Finset.mem_range.mp hkMem
  unfold affinePathTerm
  rw [R.prefixTwoDepth_blockWord_eq_of_right hRight hEnd hk]
  simp
  omega

/-- compact-support interval の完全な左側では local decoration area が不変。 -/
theorem localDecorationArea_blockWord_eq_of_left
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len : ℕ}
    (hEnd : start + len ≤ a) :
    localDecorationArea (blockWord u start len) =
      localDecorationArea (blockWord v start len) := by
  have hEndP : start + len ≤ p := by
    have hac := R.start_lt_stop
    have hcp := R.stop_le_terminal
    omega
  have hOddU : oddSteps (blockWord u start len) = len :=
    oddSteps_blockWord u hEndP
  have hOddV : oddSteps (blockWord v start len) = len :=
    oddSteps_blockWord v hEndP
  unfold localDecorationArea
  rw [R.affineConst_blockWord_eq_of_left hEnd, hOddU, hOddV]

/-- compact-support interval の完全な右側でも local decoration area が不変。 -/
theorem localDecorationArea_blockWord_eq_of_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len : ℕ}
    (hRight : c ≤ start)
    (hEnd : start + len ≤ p) :
    localDecorationArea (blockWord u start len) =
      localDecorationArea (blockWord v start len) := by
  have hOddU : oddSteps (blockWord u start len) = len :=
    oddSteps_blockWord u hEnd
  have hOddV : oddSteps (blockWord v start len) = len :=
    oddSteps_blockWord v hEnd
  unfold localDecorationArea
  rw [R.affineConst_blockWord_eq_of_right hRight hEnd, hOddU, hOddV]

end BlockReplacement

/-! ## 2. P27 flatIntervalTarget の merged local area は 0 -/

/--
P27 の `flatIntervalTarget` で平坦化された interval 全体を一つの local block として見ると、
その `localDecorationArea` は exact に 0。

これは canonical area merge の false branch が merged factor を
`flatAreaValue` に置くことと同じ局所 datum である。
-/
theorem flatIntervalTarget_mergedLocalDecorationArea_eq_zero
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c len : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    (hLen : a + len = c) :
    localDecorationArea
        (blockWord
          (flatIntervalTarget u a c hac hcp hRoofA hRight)
          a len) = 0 := by
  let v := flatIntervalTarget u a c hac hcp hRoofA hRight
  have hEnd : a + len ≤ p := by
    rw [hLen]
    exact hcp
  have hRoofV : RoofContact v a := by
    dsimp [v]
    exact flatIntervalTarget_leftRoof
      u a c hac hcp hRoofA hRight
  have hVExA : v.excessAt a = criticalExcess a :=
    excessAt_eq_criticalExcess_of_roof hRoofV
  have hFlat :
      ∀ k : ℕ,
        k < len →
        v.excessAt (a + k) = v.excessAt a := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      have hInside : a < a + k := by omega
      have hBeforeC : a + k < c := by omega
      have hBeforeP : a + k < p := lt_of_lt_of_le hBeforeC hcp
      have hHeight :=
        flatIntervalTarget_height
          u a c hac hcp hRoofA hRight hBeforeP
      have hExShape :
          flatIntervalExcess u a c (a + k) = criticalExcess a :=
        flatIntervalExcess_of_inside
          u a c (a + k) hInside hBeforeC
      rw [hExShape] at hHeight
      have hHeightEx :=
        v.height_eq_index_add_excess (Nat.le_of_lt hBeforeP)
      have hInsideEx : v.excessAt (a + k) = criticalExcess a := by
        have hHeight' :
          v.height (a + k) =
            a + k + criticalExcess a := by
          simpa [v] using hHeight
        omega
      exact hInsideEx.trans hVExA.symm
  have hAffine :
      affineConst (blockWord v a len) = baseAffineConst len :=
    affineConst_blockWord_eq_baseAffineConst_of_flat_interval
      v hEnd hFlat
  have hOdd : oddSteps (blockWord v a len) = len :=
    oddSteps_blockWord v hEnd
  unfold localDecorationArea
  rw [hAffine, hOdd]
  simp

/--
P27 flat interval target は compact support を持ち、
同時に merged interval の local area を 0 にする。
-/
structure P27FlatIntervalAreaCompatibility
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) : Prop where
  replacement :
    BlockReplacement u
      (flatIntervalTarget u a c hac hcp hRoofA hRight) a c
  merged_area_zero :
    localDecorationArea
        (blockWord
          (flatIntervalTarget u a c hac hcp hRoofA hRight)
          a (c - a)) = 0

/-- P27 flat interval target の area-level compact-support compatibility。 -/
theorem p27FlatIntervalAreaCompatibility
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) :
    P27FlatIntervalAreaCompatibility
      u a c hac hcp hRoofA hRight := by
  refine {
    replacement :=
      flatIntervalTarget_blockReplacement
        u a c hac hcp hRoofA hRight
    merged_area_zero := ?_
  }
  have hLen : a + (c - a) = c := by omega
  exact flatIntervalTarget_mergedLocalDecorationArea_eq_zero
    u a c (c - a) hac hcp hRoofA hRight hLen

/-! ## 3. canonical target は area vector で一意 -/

/--
任意の downward move `R -> S` について、target actual fiber の点 `Y` が
canonical recursive evaluator と同じ area vector を持てば、`Y` は canonical actual target
そのものに一致する。

P27/P28 target と canonical target を比較するときの主 uniqueness port。
-/
theorem boundaryDecorationActualCanonicalInterfiberCoarsening_eq_of_values
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R)
    (Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D S)
    (hValues :
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D S Y).values =
        LocalAreaTuple.canonicalCoarsenValues
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).values
          (relativeBoundaryFlags R S)) :
    Y =
      boundaryDecorationActualCanonicalInterfiberCoarsening
        P hPrimitive hReduced u D hSR X := by
  apply (boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D S).injective
  apply LocalAreaTuple.eq_of_values_eq
  calc
    (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D S Y).values
        = LocalAreaTuple.canonicalCoarsenValues
            (boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R X).values
            (relativeBoundaryFlags R S) := hValues
    _ =
      (boundaryDecorationCanonicalInterfiberCoarsening
        D hSR
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X)).values := by
        symm
        exact boundaryDecorationCanonicalInterfiberCoarsening_values
          D hSR
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X)
    _ =
      (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D S
        (boundaryDecorationActualCanonicalInterfiberCoarsening
          P hPrimitive hReduced u D hSR X)).values := by
        rw [boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate]

/--
one-boundary specialization: canonical area-vector formula を持つ actual target は
canonical one-boundary target に一致する。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_eq_of_values
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R)
    (Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D
      (eraseRetainedBoundary R b))
    (hValues :
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) Y).values =
        LocalAreaTuple.canonicalCoarsenValues
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).values
          (relativeBoundaryFlags R (eraseRetainedBoundary R b))) :
    Y =
      boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b X := by
  exact boundaryDecorationActualCanonicalInterfiberCoarsening_eq_of_values
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b) X Y hValues

/--
compact-support target `Y` が canonical area-vector formula を満たすなら、
canonical target 自身も同じ support interval の `BlockReplacement` である。

したがって P27/P28 target の vector formula を確立した時点で、
compact support は canonical map へ自動 transport される。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_blockReplacement_of_values
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R)
    (Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D
      (eraseRetainedBoundary R b))
    (a c : ℕ)
    (hRep : BlockReplacement X.1 Y.1 a c)
    (hValues :
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) Y).values =
        LocalAreaTuple.canonicalCoarsenValues
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).values
          (relativeBoundaryFlags R (eraseRetainedBoundary R b))) :
    BlockReplacement
      X.1
      (boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b X).1
      a c := by
  have hEq :=
    boundaryDecorationActualCanonicalInterfiberMerge_eq_of_values
      P hPrimitive hReduced u D R b X Y hValues
  rw [← hEq]
  exact hRep

/-! ## 4. flat fibers は canonical transport で flat のまま -/

/-- flat local-decoration tuple の area vector は全成分 0。 -/
theorem flatLocalDecorationTuple_toLocalAreaTuple_values_all_zero
    (rs : List ℕ)
    (hPos : ∀ r ∈ rs, 0 < r) :
    ∀ a ∈
      (flatLocalDecorationTuple rs hPos).toLocalAreaTuple.values,
      a = 0 := by
  induction rs with
  | nil =>
      intro a ha
      simp [flatLocalDecorationTuple,
        LocalDecorationTuple.toLocalAreaTuple] at ha
  | cons r rs ih =>
      let hr : 0 < r := hPos r (by simp)
      let hTailPos : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hPos s (by simp [hs])
      intro a ha
      change
        a ∈
          localDecorationArea (localFlatDecoration r hr).word ::
            (flatLocalDecorationTuple rs hTailPos).toLocalAreaTuple.values
        at ha
      simp only [List.mem_cons] at ha
      rcases ha with ha | ha
      · subst a
        exact localDecorationArea_localFlatDecoration_eq_zero r hr
      · exact ih hTailPos a ha

/-- bundle flat fiber の area vector は全成分 0。 -/
theorem boundaryDecorationFlatFiber_values_all_zero
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ∀ a ∈ (boundaryDecorationFlatFiber D R).values,
      a = 0 := by
  unfold boundaryDecorationFlatFiber
  exact flatLocalDecorationTuple_toLocalAreaTuple_values_all_zero
    (coarsenedLengthsFor D R)
    (coarsenedLengthsFor_pos D R)

/-- `flattenHeadAreaValues` は all-zero 性を保存する。 -/
theorem LocalAreaTuple.flattenHeadAreaValues_all_zero
    {xs : List ℕ}
    (hZero : ∀ a ∈ xs, a = 0) :
    ∀ a ∈ LocalAreaTuple.flattenHeadAreaValues xs, a = 0 := by
  cases xs with
  | nil =>
      intro a ha
      simp only [flattenHeadAreaValues, List.mem_cons, List.not_mem_nil, or_false] at ha
      exact ha
  | cons x xs =>
      intro a ha
      simp only [LocalAreaTuple.flattenHeadAreaValues, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact hZero a (by simp [ha])

/--
all-zero な head と、再帰的に all-zero を保つ tail が与えられれば、
一個の boundary flag を処理した後の canonical area vector も all-zero。

`keep = true` では head の 0 をそのまま保持し、
`keep = false` では zero tail に対する head flatten が zero を保つ。
-/
private theorem LocalAreaTuple.canonicalCoarsenValues_cons_all_zero
    {x y : ℕ}
    {ys : List ℕ}
    (hx : x = 0)
    (more : List Bool)
    (hTail :
      ∀ z ∈ LocalAreaTuple.canonicalCoarsenValues (y :: ys) more,
        z = 0)
    (keep : Bool) :
    ∀ z ∈
      LocalAreaTuple.canonicalCoarsenValues
        (x :: y :: ys) (keep :: more),
      z = 0 := by
  cases keep with
  | true =>
      intro z hz
      simp only [
        LocalAreaTuple.canonicalCoarsenValues,
        List.mem_cons
      ] at hz
      rcases hz with hzx | hz
      · exact hzx.trans hx
      · exact hTail z hz
  | false =>
      exact
        LocalAreaTuple.flattenHeadAreaValues_all_zero hTail

/--
pure canonical area evaluator は all-zero area vector を all-zero のまま保つ。

各 recursive step では、boundary を保持する場合は zero head をそのまま残し、
boundary を削除する場合は zero tail に対する head flatten を行う。
従って任意の boundary flags に対して zero area は不変である。
-/
theorem LocalAreaTuple.canonicalCoarsenValues_all_zero
    {xs : List ℕ}
    (hZero : ∀ a ∈ xs, a = 0)
    (flags : List Bool) :
    ∀ a ∈ LocalAreaTuple.canonicalCoarsenValues xs flags, a = 0 := by
  induction xs generalizing flags with
  | nil =>
      intro z hz
      simp [LocalAreaTuple.canonicalCoarsenValues] at hz
  | cons x rest ih =>
      have hx : x = 0 :=
        hZero x (by simp)
      cases rest with
      | nil =>
          intro z hz
          simp only [
            LocalAreaTuple.canonicalCoarsenValues,
            List.mem_cons,
            List.not_mem_nil,
            or_false
          ] at hz
          exact hz.trans hx
      | cons y ys =>
          have hTailZero :
              ∀ z ∈ y :: ys, z = 0 := by
            intro z hz
            exact hZero z (by simp [hz])
          cases flags with
          | nil =>
              intro z hz
              exact hZero z hz
          | cons keep more =>
              have hRec :
                  ∀ z ∈
                    LocalAreaTuple.canonicalCoarsenValues
                      (y :: ys) more,
                    z = 0 :=
                ih hTailZero more
              exact
                LocalAreaTuple.canonicalCoarsenValues_cons_all_zero
                  hx more hRec keep

/--
同じ長さの二つの all-zero list は同一。
-/
theorem list_eq_of_all_zero_of_length_eq
    {xs ys : List ℕ}
    (hx : ∀ a ∈ xs, a = 0)
    (hy : ∀ a ∈ ys, a = 0)
    (hLen : xs.length = ys.length) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      have hY : ys = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hLen.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hLen
      | cons y ys =>
          have hx0 : x = 0 := hx x (by simp)
          have hy0 : y = 0 := hy y (by simp)
          subst x
          subst y
          have hTailLen : xs.length = ys.length := by
            simpa using hLen
          have hxTail : ∀ a ∈ xs, a = 0 := by
            intro a ha
            exact hx a (by simp [ha])
          have hyTail : ∀ a ∈ ys, a = 0 := by
            intro a ha
            exact hy a (by simp [ha])
          rw [ih hxTail hyTail hTailLen]

/--
canonical downward transport は all-flat fiber section を
all-flat fiber section へ送る。

これは任意の Boolean downward move `S ≤ R` に対して成立する。
pure canonical coarsening は zero area vector を zero のまま保ち、
source / target の fiber index が同じ target coarse skeleton に一致するため。
-/
theorem boundaryDecorationCanonicalInterfiberCoarsening_flatFiber
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    boundaryDecorationCanonicalInterfiberCoarsening
        D hSR (boundaryDecorationFlatFiber D R) =
      boundaryDecorationFlatFiber D S := by
  apply LocalAreaTuple.eq_of_values_eq
  have hLen :
      (boundaryDecorationCanonicalInterfiberCoarsening
          D hSR (boundaryDecorationFlatFiber D R)).values.length =
        (boundaryDecorationFlatFiber D S).values.length := by
    have hLeft :=
      (boundaryDecorationCanonicalInterfiberCoarsening
        D hSR (boundaryDecorationFlatFiber D R)).values_length
    have hRight :=
      (boundaryDecorationFlatFiber D S).values_length
    exact hLeft.trans hRight.symm
  rw [boundaryDecorationCanonicalInterfiberCoarsening_values] at hLen ⊢
  apply list_eq_of_all_zero_of_length_eq
  · exact LocalAreaTuple.canonicalCoarsenValues_all_zero
      (boundaryDecorationFlatFiber_values_all_zero D R)
      (relativeBoundaryFlags R S)
  · exact boundaryDecorationFlatFiber_values_all_zero D S
  · exact hLen

/-- one-boundary specialization of flat-fiber preservation。 -/
theorem boundaryDecorationCanonicalInterfiberMerge_flatFiber
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    boundaryDecorationCanonicalInterfiberMerge
        D R b (boundaryDecorationFlatFiber D R) =
      boundaryDecorationFlatFiber D (eraseRetainedBoundary R b) := by
  exact boundaryDecorationCanonicalInterfiberCoarsening_flatFiber
    D (eraseRetainedBoundary_le R b)

/-! ## 5. flat section では actual canonical boundary deletion と exact に一致 -/

/-- base `R` の canonical all-flat actual fiber point。 -/
noncomputable def boundaryDecorationActualFlatFiber
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R :=
  (boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D R).symm
    (boundaryDecorationFlatFiber D R)

/-- actual flat fiber point の abstract coordinate は flat fiber そのもの。 -/
@[simp] theorem boundaryDecorationActualFlatFiber_coordinate
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R
        (boundaryDecorationActualFlatFiber
          P hPrimitive hReduced u D R) =
      boundaryDecorationFlatFiber D R := by
  exact (boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D R).apply_symm_apply _

/-- actual flat fiber point の underlying FiberPoint は base canonical flat point。 -/
theorem boundaryDecorationActualFlatFiber_point
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    (boundaryDecorationActualFlatFiber
      P hPrimitive hReduced u D R).1 =
      canonicalFlatPoint P hPrimitive hReduced u D R := by
  apply fiberPoint_eq_of_same_affineConst
  let X := boundaryDecorationActualFlatFiber
    P hPrimitive hReduced u D R
  have hAffine :=
    boundaryDecorationActualFiber_affineConst_eq_flatAffine_add_two_mul_weightedArea
      P hPrimitive hReduced u D R X
  have hCoord :
      boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X =
        boundaryDecorationFlatFiber D R := by
    dsimp [X]
    exact boundaryDecorationActualFlatFiber_coordinate
      P hPrimitive hReduced u D R
  have hArea :
      (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R X).weightedArea = 0 := by
    rw [hCoord]
    exact boundaryDecorationFlatFiber_weightedArea_eq_zero D R
  rw [hArea] at hAffine
  simpa [X, flatAffine] using hAffine

/-- arbitrary downward canonical actual transport は actual flat point を flat pointへ送る。 -/
theorem boundaryDecorationActualCanonicalInterfiberCoarsening_flat
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    boundaryDecorationActualCanonicalInterfiberCoarsening
        P hPrimitive hReduced u D hSR
        (boundaryDecorationActualFlatFiber
          P hPrimitive hReduced u D R) =
      boundaryDecorationActualFlatFiber
        P hPrimitive hReduced u D S := by
  apply (boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D S).injective
  rw [boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate]
  rw [boundaryDecorationActualFlatFiber_coordinate]
  rw [boundaryDecorationActualFlatFiber_coordinate]
  exact boundaryDecorationCanonicalInterfiberCoarsening_flatFiber D hSR

/-- one-boundary canonical actual merge も flat section を exact に保つ。 -/
theorem boundaryDecorationActualCanonicalInterfiberMerge_flat
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b
        (boundaryDecorationActualFlatFiber
          P hPrimitive hReduced u D R) =
      boundaryDecorationActualFlatFiber
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b) := by
  exact boundaryDecorationActualCanonicalInterfiberCoarsening_flat
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b)

/--
flat section の canonical one-boundary merge は、underlying FiberPoint として
P31--P34 の canonical flat boundary deletion endpoint に exact に一致する。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_flat_point
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    (boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b
        (boundaryDecorationActualFlatFiber
          P hPrimitive hReduced u D R)).1 =
      canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundary R b) := by
  rw [boundaryDecorationActualCanonicalInterfiberMerge_flat]
  exact boundaryDecorationActualFlatFiber_point
    P hPrimitive hReduced u D (eraseRetainedBoundary R b)

/--
flat section 上では canonical merge は P34 の actual `BlockReplacement` geometry と一致する。
P34 の現行 API が与える support は `[1,p]`。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_flat_blockReplacement
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    BlockReplacement
      (boundaryDecorationActualFlatFiber
        P hPrimitive hReduced u D R).1
      (boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b
        (boundaryDecorationActualFlatFiber
          P hPrimitive hReduced u D R)).1
      1 P.oddCount := by
  rw [
    boundaryDecorationActualFlatFiber_point,
    boundaryDecorationActualCanonicalInterfiberMerge_flat_point
  ]
  exact canonicalFlatPoint_blockReplacement_one_terminal
    P hPrimitive hReduced u D
    R (eraseRetainedBoundary R b)

/-! ## 6. closure package -/

/--
canonical merge / actual compact-support compatibility 層で閉じた data。

* P27 flat interval target は genuine `BlockReplacement` かつ merged local area 0。
* `BlockReplacement` の外側 local area は exact に保存。
* canonical area vector を持つ target は canonical actual target に一意。
* flat section では canonical merge と P34 actual boundary deletion endpoint が exact に一致。
-/
structure BoundaryDecorationCanonicalMergeActualCompatibilityClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  canonical_unique_by_values :
    ∀ {R S : RetainedBoundaryPattern D}
      (hSR : S.Le R)
      (X : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R)
      (Y : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D S),
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D S Y).values =
        LocalAreaTuple.canonicalCoarsenValues
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).values
          (relativeBoundaryFlags R S) →
      Y = boundaryDecorationActualCanonicalInterfiberCoarsening
        P hPrimitive hReduced u D hSR X

  flat_section_exact :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D),
      (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b
          (boundaryDecorationActualFlatFiber
            P hPrimitive hReduced u D R)).1 =
        canonicalFlatPoint P hPrimitive hReduced u D
          (eraseRetainedBoundary R b)

  flat_section_replacement :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D),
      BlockReplacement
        (boundaryDecorationActualFlatFiber
          P hPrimitive hReduced u D R).1
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b
          (boundaryDecorationActualFlatFiber
            P hPrimitive hReduced u D R)).1
        1 P.oddCount

/-- Canonical merge actual compatibility closure theorem。 -/
theorem boundaryDecorationCanonicalMergeActualCompatibility_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationCanonicalMergeActualCompatibilityClosed
      P hPrimitive hReduced u D := by
  refine {
    canonical_unique_by_values := ?_
    flat_section_exact := ?_
    flat_section_replacement := ?_
  }
  · intro R S hSR X Y hValues
    exact boundaryDecorationActualCanonicalInterfiberCoarsening_eq_of_values
      P hPrimitive hReduced u D hSR X Y hValues
  · intro R b
    exact boundaryDecorationActualCanonicalInterfiberMerge_flat_point
      P hPrimitive hReduced u D R b
  · intro R b
    exact boundaryDecorationActualCanonicalInterfiberMerge_flat_blockReplacement
      P hPrimitive hReduced u D R b

end RecordFerrers
end Collatz2
