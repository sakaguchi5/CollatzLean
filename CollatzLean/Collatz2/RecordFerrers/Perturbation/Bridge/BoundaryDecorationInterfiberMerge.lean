import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationArithmeticExactness
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P33BooleanFerrersOrderEmbedding

/-!
# Record–Ferrers Perturbation / Boundary Decoration Interfiber Merge

`BoundaryDecorationBundle` では retained-boundary pattern `R` の上に

  LocalAreaTuple (coarsenedLengthsFor D R)

を fiber として載せた。しかし boundary を一つ削除すると length skeleton 自体が変わるため、
非平坦な decorated point を別 fiber へ送る transport はまだ未構成だった。

本ファイルでは P27--P29 の actual coarsening engine を bundle fiber 間へ持ち上げる。

鍵は「二段階粗視化の合成則」である。`S.Le R` のとき、元 boundary flags のうち
`R` に残っている位置だけを読み、その位置で `S` が残すか消すかを並べた relative flags
を定義する。すると

  coarsenByFlags (coarsenByFlags lengths flagsR) relativeFlags
    = coarsenByFlags lengths flagsS

が exact に成立する。

従って pattern `R` の arbitrary actual decorated source `X` の chosen decomposition に
relative flags を適用すれば、P29 `RecordChain.exists_actual_coarsening_of_flags` により
pattern `S` の coarse skeleton を持つ actual FirstCrossing target が存在する。

特に

  S = eraseRetainedBoundary R b,  R b = true

とすれば、一つの retained boundary を消す inter-fiber merge が得られる。
P29 の actual coarsening は内部で P28、さらに P27 の direct record-run merge を使うので、
これは単なる abstract existence ではなく既存 actual merge geometry の bundle-level transport
である。

注意:
本ファイルでは「target skeleton が exact に S であること」と「任意 R-fiber source から
actual target が存在すること」を閉じる。P27 の compact support を bundle coordinate の
『変更されない各 factor / merged flat factor』へ exact に読み戻す refinement は、
この inter-fiber existence の次段として分離する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. relative boundary flags -/

/--
`upper` で残っている boundary だけを走査し、その位置で `lower` が境界を残すかを読む。

想定は `BoolListLe lower upper`。
`upper = false` の位置は既に coarse skeleton から消えているので出力しない。
-/
def relativeBoundaryFlagsList : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | u :: us, l :: ls =>
      if u then l :: relativeBoundaryFlagsList us ls
      else relativeBoundaryFlagsList us ls

/-- `mergeHeadLength` は nonempty list の block 数を変えない。 -/
theorem mergeHeadLength_length_of_nonempty
    (r : ℕ)
    {xs : List ℕ}
    (hxs : xs ≠ []) :
    (mergeHeadLength r xs).length = xs.length := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs => simp [mergeHeadLength]

/-- 二回の先頭吸収は加法的に合成する。 -/
theorem mergeHeadLength_add
    (r s : ℕ)
    {xs : List ℕ}
    (hxs : xs ≠ []) :
    mergeHeadLength (r + s) xs =
      mergeHeadLength r (mergeHeadLength s xs) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs =>
      simp [mergeHeadLength, Nat.add_assoc]

/--
先頭 block を既に吸収した後で Bool 粗視化しても、先に Bool 粗視化してから
同じ先頭 block を吸収しても一致する。
-/
theorem coarsenByFlags_mergeHeadLength
    (r : ℕ)
    {xs : List ℕ}
    (hxs : xs ≠ [])
    (flags : List Bool)
    (hFlags : flags.length = xs.length - 1) :
    coarsenByFlags (mergeHeadLength r xs) flags =
      mergeHeadLength r (coarsenByFlags xs flags) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x tail =>
      cases tail with
      | nil =>
          have hNil : flags = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using hFlags
          subst flags
          simp [mergeHeadLength, coarsenByFlags]
      | cons y ys =>
          cases flags with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hFlags
              omega
          | cons b bs =>
              have hTailNe :
                  coarsenByFlags (y :: ys) bs ≠ [] :=
                coarsenByFlags_nonempty (by simp) bs
              cases b with
              | true =>
                  simp [mergeHeadLength, coarsenByFlags]
              | false =>
                  simp only [mergeHeadLength, coarsenByFlags]
                  exact mergeHeadLength_add r x hTailNe

/--
先頭 boundary が upper では保持、lower では削除される場合の relative coarsening step。

tail 上で relative coarsening composition が成立していれば、
先頭 relative flag は `false` となり、全体でも同じ composition が成立する。
-/
private theorem relativeBoundaryFlagsList_spec_head_true_false
    (r s : ℕ)
    (tail : List ℕ)
    (us ls : List Bool)
    (hQLen :
      (relativeBoundaryFlagsList us ls).length =
        (coarsenByFlags (s :: tail) us).length - 1)
    (hQCoarsen :
      coarsenByFlags
          (coarsenByFlags (s :: tail) us)
          (relativeBoundaryFlagsList us ls) =
        coarsenByFlags (s :: tail) ls) :
    (relativeBoundaryFlagsList (true :: us) (false :: ls)).length =
        (coarsenByFlags
          (r :: s :: tail) (true :: us)).length - 1 ∧
      coarsenByFlags
          (coarsenByFlags
            (r :: s :: tail) (true :: us))
          (relativeBoundaryFlagsList
            (true :: us) (false :: ls)) =
        coarsenByFlags
          (r :: s :: tail) (false :: ls) := by
  have hRestNe : (s :: tail) ≠ [] := by
    simp
  have hUpperTailNe :
      coarsenByFlags (s :: tail) us ≠ [] :=
    coarsenByFlags_nonempty hRestNe us
  have hUpperTailLenPos :
      0 < (coarsenByFlags (s :: tail) us).length :=
    List.length_pos_iff.mpr hUpperTailNe
  constructor
  · change
      (false :: relativeBoundaryFlagsList us ls).length =
        (coarsenByFlags
          (r :: s :: tail) (true :: us)).length - 1
    simp only [List.length_cons]
    rw [coarsenByFlags_cons_true r hRestNe us]
    simp only [List.length_cons]
    omega
  · change
      coarsenByFlags
          (coarsenByFlags
            (r :: s :: tail) (true :: us))
          (false :: relativeBoundaryFlagsList us ls) =
        coarsenByFlags
          (r :: s :: tail) (false :: ls)
    rw [coarsenByFlags_cons_true r hRestNe us]
    rw [coarsenByFlags_cons_false r hRestNe ls]
    rw [coarsenByFlags_cons_false
      r hUpperTailNe (relativeBoundaryFlagsList us ls)]
    rw [hQCoarsen]

/--
先頭 boundary が upper / lower の双方で保持される場合の relative coarsening step。

tail 上で composition が成立していれば、
先頭 relative flag は `true` となり、全体でも composition が成立する。
-/
private theorem relativeBoundaryFlagsList_spec_head_true_true
    (r s : ℕ)
    (tail : List ℕ)
    (us ls : List Bool)
    (hQLen :
      (relativeBoundaryFlagsList us ls).length =
        (coarsenByFlags (s :: tail) us).length - 1)
    (hQCoarsen :
      coarsenByFlags
          (coarsenByFlags (s :: tail) us)
          (relativeBoundaryFlagsList us ls) =
        coarsenByFlags (s :: tail) ls) :
    (relativeBoundaryFlagsList (true :: us) (true :: ls)).length =
        (coarsenByFlags
          (r :: s :: tail) (true :: us)).length - 1 ∧
      coarsenByFlags
          (coarsenByFlags
            (r :: s :: tail) (true :: us))
          (relativeBoundaryFlagsList
            (true :: us) (true :: ls)) =
        coarsenByFlags
          (r :: s :: tail) (true :: ls) := by
  have hRestNe : (s :: tail) ≠ [] := by
    simp
  have hUpperTailNe :
      coarsenByFlags (s :: tail) us ≠ [] :=
    coarsenByFlags_nonempty hRestNe us
  have hUpperTailLenPos :
      0 < (coarsenByFlags (s :: tail) us).length :=
    List.length_pos_iff.mpr hUpperTailNe
  constructor
  · change
      (true :: relativeBoundaryFlagsList us ls).length =
        (coarsenByFlags
          (r :: s :: tail) (true :: us)).length - 1
    simp only [List.length_cons]
    rw [coarsenByFlags_cons_true r hRestNe us]
    simp only [List.length_cons]
    omega
  · change
      coarsenByFlags
          (coarsenByFlags
            (r :: s :: tail) (true :: us))
          (true :: relativeBoundaryFlagsList us ls) =
        coarsenByFlags
          (r :: s :: tail) (true :: ls)
    rw [coarsenByFlags_cons_true r hRestNe us]
    rw [coarsenByFlags_cons_true r hRestNe ls]
    rw [coarsenByFlags_cons_true
      r hUpperTailNe (relativeBoundaryFlagsList us ls)]
    rw [hQCoarsen]

/--
先頭 boundary が upper / lower の双方ですでに削除される場合の relative coarsening step。

先頭では新たな relative operation は発生せず、
tail の relative flags をそのまま用いる。
`mergeHeadLength` と relative coarsening が可換であることから composition が従う。
-/
private theorem relativeBoundaryFlagsList_spec_head_false_false
    (r s : ℕ)
    (tail : List ℕ)
    (us ls : List Bool)
    (hQLen :
      (relativeBoundaryFlagsList us ls).length =
        (coarsenByFlags (s :: tail) us).length - 1)
    (hQCoarsen :
      coarsenByFlags
          (coarsenByFlags (s :: tail) us)
          (relativeBoundaryFlagsList us ls) =
        coarsenByFlags (s :: tail) ls) :
    (relativeBoundaryFlagsList (false :: us) (false :: ls)).length =
        (coarsenByFlags
          (r :: s :: tail) (false :: us)).length - 1 ∧
      coarsenByFlags
          (coarsenByFlags
            (r :: s :: tail) (false :: us))
          (relativeBoundaryFlagsList
            (false :: us) (false :: ls)) =
        coarsenByFlags
          (r :: s :: tail) (false :: ls) := by
  have hRestNe : (s :: tail) ≠ [] := by
    simp
  have hUpperTailNe :
      coarsenByFlags (s :: tail) us ≠ [] :=
    coarsenByFlags_nonempty hRestNe us
  have hMergedLen :
      (mergeHeadLength r
        (coarsenByFlags (s :: tail) us)).length =
        (coarsenByFlags (s :: tail) us).length :=
    mergeHeadLength_length_of_nonempty
      r hUpperTailNe
  constructor
  · change
      (relativeBoundaryFlagsList us ls).length =
        (coarsenByFlags
          (r :: s :: tail) (false :: us)).length - 1
    rw [coarsenByFlags_cons_false r hRestNe us]
    rw [hMergedLen]
    exact hQLen
  · change
      coarsenByFlags
          (coarsenByFlags
            (r :: s :: tail) (false :: us))
          (relativeBoundaryFlagsList us ls) =
        coarsenByFlags
          (r :: s :: tail) (false :: ls)
    rw [coarsenByFlags_cons_false r hRestNe us]
    rw [coarsenByFlags_cons_false r hRestNe ls]
    rw [coarsenByFlags_mergeHeadLength
      r
      hUpperTailNe
      (relativeBoundaryFlagsList us ls)
      hQLen]
    rw [hQCoarsen]

/--
## Relative Coarsening Composition

`lower ≤ upper` の Bool boundary flags に対して、
`upper` まで粗視化した skeleton を relative flags でさらに粗視化すると、
`lower` まで一度に粗視化した skeleton と exact に一致する。

同時に relative flags の長さが、
current coarse skeleton の内部境界数と一致することも示す。
-/
theorem relativeBoundaryFlagsList_spec
    (lengths : List ℕ)
    (upper lower : List Bool)
    (hUpper : upper.length = lengths.length - 1)
    (hLower : lower.length = lengths.length - 1)
    (hLe : BoolListLe lower upper) :
    let q := relativeBoundaryFlagsList upper lower
    q.length = (coarsenByFlags lengths upper).length - 1 ∧
      coarsenByFlags
          (coarsenByFlags lengths upper) q =
        coarsenByFlags lengths lower := by
  induction lengths generalizing upper lower with
  | nil =>
      have hU : upper = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hUpper
      have hL : lower = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hLower
      subst upper
      subst lower
      simp [relativeBoundaryFlagsList, coarsenByFlags]
  | cons r rest ih =>
      cases rest with
      | nil =>
          have hU : upper = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using hUpper
          have hL : lower = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using hLower
          subst upper
          subst lower
          simp [relativeBoundaryFlagsList, coarsenByFlags]
      | cons s tail =>
          cases upper with
          | nil =>
              simp only [
                List.length_nil,
                List.length_cons
              ] at hUpper
              omega
          | cons ub us =>
              cases lower with
              | nil =>
                  simp only [
                    List.length_nil,
                    List.length_cons
                  ] at hLower
                  omega
              | cons lb ls =>
                  have hUs :
                      us.length =
                        (s :: tail).length - 1 := by
                    simp only [List.length_cons] at hUpper ⊢
                    omega
                  have hLs :
                      ls.length =
                        (s :: tail).length - 1 := by
                    simp only [List.length_cons] at hLower ⊢
                    omega
                  simp only [BoolListLe] at hLe
                  have hIH :=
                    ih us ls
                      hUs hLs hLe.2
                  have hQLen :
                      (relativeBoundaryFlagsList us ls).length =
                        (coarsenByFlags
                          (s :: tail) us).length - 1 := by
                    exact hIH.1
                  have hQCoarsen :
                      coarsenByFlags
                          (coarsenByFlags
                            (s :: tail) us)
                          (relativeBoundaryFlagsList us ls) =
                        coarsenByFlags
                          (s :: tail) ls := by
                    exact hIH.2
                  cases ub with
                  | true =>
                      cases lb with
                      | false =>
                          simpa using
                            relativeBoundaryFlagsList_spec_head_true_false
                              r s tail us ls
                              hQLen hQCoarsen
                      | true =>
                          simpa using
                            relativeBoundaryFlagsList_spec_head_true_true
                              r s tail us ls
                              hQLen hQCoarsen
                  | false =>
                      have hLbFalse : lb = false := by
                        cases lb with
                        | false =>
                            rfl
                        | true =>
                            exfalso
                            have hBad := hLe.1 rfl
                            simp at hBad
                      subst lb
                      simpa using
                        relativeBoundaryFlagsList_spec_head_false_false
                          r s tail us ls
                          hQLen hQCoarsen




/-! ## 2. retained patterns 上の relative flags -/

/-- `R` から `S ≤ R` へ進むために current coarse skeleton 上で読む relative flags。 -/
def relativeBoundaryFlags
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) : List Bool :=
  relativeBoundaryFlagsList (retainedFlags R) (retainedFlags S)

/--
pattern inclusion に対する relative flags の exact specification。
-/
theorem relativeBoundaryFlags_spec
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    (relativeBoundaryFlags R S).length =
        (coarsenedLengthsFor D R).length - 1 ∧
      coarsenByFlags
          (coarsenedLengthsFor D R)
          (relativeBoundaryFlags R S) =
        coarsenedLengthsFor D S := by
  unfold relativeBoundaryFlags coarsenedLengthsFor
  exact relativeBoundaryFlagsList_spec
    D.lengths
    (retainedFlags R)
    (retainedFlags S)
    (retainedFlags_length R)
    (retainedFlags_length S)
    (retainedFlags_le hSR)

/-- 一境界削除用 relative flags は current coarse skeleton に対して有効。 -/
theorem relativeBoundaryFlags_erase_length
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    (relativeBoundaryFlags R (eraseRetainedBoundary R b)).length =
      (coarsenedLengthsFor D R).length - 1 :=
  (relativeBoundaryFlags_spec D
    (eraseRetainedBoundary_le R b)).1

/-- 一境界削除用 relative flags は target coarse skeleton を exact に作る。 -/
theorem coarsenByFlags_relativeBoundaryFlags_erase
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    coarsenByFlags
        (coarsenedLengthsFor D R)
        (relativeBoundaryFlags R (eraseRetainedBoundary R b)) =
      coarsenedLengthsFor D (eraseRetainedBoundary R b) :=
  (relativeBoundaryFlags_spec D
    (eraseRetainedBoundary_le R b)).2

/-! ## 3. arbitrary actual fiber source の downward inter-fiber coarsening -/

/--
`S.Le R` のとき、arbitrary actual `R`-fiber source から `S`-fiber source へ
P29 actual coarsening により到達できる。

P29 の proof は `false` flag ごとに P28 direct coarsening を呼び、P28 は P27 の
actual direct record-run merge を使う。従ってこの存在定理は coarse skeleton の型合わせだけでなく、
既存の actual merge construction をそのまま再利用している。
-/
theorem exists_boundaryDecorationActualInterfiberCoarsening
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    ∃ Y : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D S,
      FirstCrossing Y.1.word := by
  let q : List Bool := relativeBoundaryFlags R S
  have hQSpec := relativeBoundaryFlags_spec D hSR
  have hXLengths :
      X.decomposition.lengths = coarsenedLengthsFor D R :=
    boundaryDecorationActualFiber_decomposition_lengths
      P hPrimitive hReduced u D R X
  have hQValid :
      q.length = X.decomposition.lengths.length - 1 := by
    dsimp [q]
    rw [hXLengths]
    exact hQSpec.1
  obtain ⟨v, out, C, hFv, hOut, _hAgree⟩ :=
    RecordChain.exists_actual_coarsening_of_flags
      P hPrimitive hReduced
      X.decomposition.chain
      X.decomposition.whole_firstCrossing
      q hQValid (by omega)
  let E : RecordDecomposition v 1 := {
    lengths := out
    chain := C
    whole_firstCrossing := hFv
  }
  have hOutTarget : out = coarsenedLengthsFor D S := by
    calc
      out = coarsenByFlags X.decomposition.lengths q := hOut
      _ = coarsenByFlags (coarsenedLengthsFor D R) q := by
            rw [hXLengths]
      _ = coarsenedLengthsFor D S := by
            exact hQSpec.2
  have hELengths :
      E.lengths = coarsenedLengthsFor D S := by
    simpa [E] using hOutTarget
  let Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D S := by
    refine ⟨v, ?_⟩
    refine ⟨E, ?_⟩
    exact hELengths.trans
      (boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D S).symm
  refine ⟨Y, ?_⟩
  simpa [Y] using hFv

/--
上の existence から一つ actual target を選ぶ canonical interface。
proof-object choice は target source の existence witness にだけ使う。
-/
noncomputable def boundaryDecorationActualInterfiberCoarsening
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D S :=
  Classical.choose
    (exists_boundaryDecorationActualInterfiberCoarsening
      P hPrimitive hReduced u D hSR X)

/-- chosen actual inter-fiber target は whole FirstCrossing。 -/
theorem boundaryDecorationActualInterfiberCoarsening_firstCrossing
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    FirstCrossing
      (boundaryDecorationActualInterfiberCoarsening
        P hPrimitive hReduced u D hSR X).1.word :=
  Classical.choose_spec
    (exists_boundaryDecorationActualInterfiberCoarsening
      P hPrimitive hReduced u D hSR X)

/-! ## 4. one-boundary inter-fiber merge -/

/--
保持されている一境界 `b` を消す actual inter-fiber merge。
-/
noncomputable def boundaryDecorationActualInterfiberMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D
      (eraseRetainedBoundary R b) :=
  boundaryDecorationActualInterfiberCoarsening
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b) X

/-- one-boundary actual merge target は whole FirstCrossing。 -/
theorem boundaryDecorationActualInterfiberMerge_firstCrossing
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    FirstCrossing
      (boundaryDecorationActualInterfiberMerge
        P hPrimitive hReduced u D R b X).1.word := by
  exact boundaryDecorationActualInterfiberCoarsening_firstCrossing
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b) X

/-- genuine one-boundary merge は base の保持境界数を exact に一つ減らす。 -/
theorem boundaryDecorationInterfiberMerge_boundaryCount
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    retainedBoundaryCount D (eraseRetainedBoundary R b) + 1 =
      retainedBoundaryCount D R :=
  retainedBoundaryCount_erase_add_one R b hb

/-! ## 5. abstract LocalArea fibers への transport -/

/-- arbitrary downward base move を abstract area-product fibers の間へ transport。 -/
noncomputable def boundaryDecorationInterfiberCoarsening
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    BoundaryDecorationFiber D R →
      BoundaryDecorationFiber D S :=
  fun A =>
    boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D S
      (boundaryDecorationActualInterfiberCoarsening
        P hPrimitive hReduced u D hSR
        ((boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R).symm A))

/-- retained one-boundary deletion の abstract inter-fiber merge map。 -/
noncomputable def boundaryDecorationInterfiberMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    BoundaryDecorationFiber D R →
      BoundaryDecorationFiber D (eraseRetainedBoundary R b) :=
  boundaryDecorationInterfiberCoarsening
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b)

/-- bundle point として one-boundary inter-fiber merge の target base は exact。 -/
noncomputable def boundaryDecorationBundleInterfiberMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (A : BoundaryDecorationFiber D R) :
    BoundaryDecorationBundle D :=
  ⟨eraseRetainedBoundary R b,
    boundaryDecorationInterfiberMerge
      P hPrimitive hReduced u D R b A⟩

@[simp] theorem boundaryDecorationBundleInterfiberMerge_base
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (A : BoundaryDecorationFiber D R) :
    (boundaryDecorationBundleInterfiberMerge
      P hPrimitive hReduced u D R b A).1 =
      eraseRetainedBoundary R b := rfl

/-! ## 6. flat section は既存 canonical boundary deletion と整合する -/

/--
flat source については、target flat fiber が既存 canonical boundary deletion の endpoint である。
これは inter-fiber extension が拡張すべき既存 flat-section geometry を固定する theorem。

ここでは上の choice-based arbitrary-source map が flat source 上で definitionally この点を選ぶとは
主張しない。flat uniqueness / compact-support refinement を追加すれば後続でその同一視を閉じられる。
-/
theorem boundaryDecorationFlatSection_oneBoundary_target
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    ∃ S : RetainedBoundaryPattern D,
      CanonicalBoundaryDeletion D R S ∧
      S = eraseRetainedBoundary R b ∧
      boundaryDecorationFlatSection D S =
        boundaryDecorationFlatSection D (eraseRetainedBoundary R b) := by
  refine ⟨eraseRetainedBoundary R b, ?_, rfl, rfl⟩
  exact ⟨b, hb, rfl⟩

/-! ## 7. closure package -/

/--
inter-fiber layer の closure data。

* arbitrary Boolean downward move は exact relative flags を持つ。
* arbitrary actual decorated source から target fiber actual source が存在する。
* genuine one-boundary deletion は bundle fiber 間の map を持つ。
-/
structure BoundaryDecorationInterfiberMergeClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  relative_flags_exact :
    ∀ {R S : RetainedBoundaryPattern D},
      S.Le R →
      coarsenByFlags
          (coarsenedLengthsFor D R)
          (relativeBoundaryFlags R S) =
        coarsenedLengthsFor D S
  arbitrary_actual_transport :
    ∀ {R S : RetainedBoundaryPattern D},
      S.Le R →
      ∀ _X : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R,
        ∃ Y : BoundaryDecorationActualFiber
            P hPrimitive hReduced u D S,
          FirstCrossing Y.1.word
  one_boundary_transport :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D),
      R b = true →
      Nonempty
        (BoundaryDecorationFiber D R →
          BoundaryDecorationFiber D
            (eraseRetainedBoundary R b))

/--
## Boundary Decoration Interfiber Merge closure theorem

P27--P29 の actual coarsening geometry は、Boolean base の任意の下向き move に対して
arbitrary decorated fiber source を target coarse-skeleton fiber へ送れる。
特に retained boundary 一個の削除ごとに abstract bundle fiber 間の merge map が存在する。
-/
theorem boundaryDecorationInterfiberMerge_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationInterfiberMergeClosed
      P hPrimitive hReduced u D := by
  refine {
    relative_flags_exact := ?_
    arbitrary_actual_transport := ?_
    one_boundary_transport := ?_
  }
  · intro R S hSR
    exact (relativeBoundaryFlags_spec D hSR).2
  · intro R S hSR X
    exact exists_boundaryDecorationActualInterfiberCoarsening
      P hPrimitive hReduced u D hSR X
  · intro R b hb
    exact ⟨boundaryDecorationInterfiberMerge
      P hPrimitive hReduced u D R b⟩

end RecordFerrers
end Collatz2
