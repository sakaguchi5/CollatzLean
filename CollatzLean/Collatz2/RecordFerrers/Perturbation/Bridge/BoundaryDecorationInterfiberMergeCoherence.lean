import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationInterfiberMergeExactness

/-!
# Record–Ferrers Perturbation / Interfiber Merge Coherence

canonical inter-fiber map は target existence の arbitrary choice ではなく、
relative boundary flags と local-area tuple の再帰から直接定義された。
本ファイルではその coherence を閉じる。

中心は三段階 `T.Le S`, `S.Le R` に対する

  C(R,T) = C(S,T) ∘ C(R,S)

である。

証明は二層に分かれる。

1. relative flags 自身が

     relative (relative R S) (relative R T) = relative S T

   を満たす。

2. pure area-vector coarsening は nested relative flags に関して exact に合成する。

最後に `LocalAreaTuple.values` の lossless 性により dependent tuple equality へ戻す。
これにより canonical downward transport は Boolean order 上で path-independent になる。
異なる二境界の base deletion は既存 `eraseRetainedBoundary_comm` により可換であり、
上の transitivity と合わせて canonical fiber transport の diamond の基礎を与える。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. relative flags の二段階 coherence -/


/--
先頭 Bool の順序条件と tail の relative flags の順序から、
cons 全体の relative flags の順序を得る局所 step。
-/
private theorem relativeBoundaryFlagsList_le_cons
    (u m l : Bool)
    (us ms ls : List Bool)
    (hMUHead : m = true → u = true)
    (hLMHead : l = true → m = true)
    (hTail :
      BoolListLe
        (relativeBoundaryFlagsList us ls)
        (relativeBoundaryFlagsList us ms)) :
    BoolListLe
      (relativeBoundaryFlagsList (u :: us) (l :: ls))
      (relativeBoundaryFlagsList (u :: us) (m :: ms)) := by
  cases u <;> cases m <;> cases l <;>
    simp_all [relativeBoundaryFlagsList, BoolListLe]


/--
`lower ≤ middle ≤ upper` なら、
`upper` 上で読む `lower`-relative flags は
`middle`-relative flags 以下になる。

すなわち、より強く boundary を削除する `lower` への relative coarsening は、
`middle` への relative coarsening を越えて boundary を保持することはない。
-/
theorem relativeBoundaryFlagsList_le
    {upper middle lower : List Bool}
    (hMU : BoolListLe middle upper)
    (hLM : BoolListLe lower middle) :
    BoolListLe
      (relativeBoundaryFlagsList upper lower)
      (relativeBoundaryFlagsList upper middle) := by
  induction upper generalizing middle lower with
  | nil =>
      cases middle with
      | nil =>
          cases lower with
          | nil =>
              trivial
          | cons l ls =>
              simp [BoolListLe] at hLM
      | cons m ms =>
          simp [BoolListLe] at hMU
  | cons u us ih =>
      cases middle with
      | nil =>
          simp [BoolListLe] at hMU
      | cons m ms =>
          cases lower with
          | nil =>
              simp [BoolListLe] at hLM
          | cons l ls =>
              simp only [BoolListLe] at hMU hLM
              have hTail := ih hMU.2 hLM.2
              exact
                relativeBoundaryFlagsList_le_cons
                  u m l us ms ls
                  hMU.1 hLM.1 hTail

/--
relative flags の relative flags は intermediate base からの relative flags そのもの。
-/
theorem relativeBoundaryFlagsList_comp
    {upper middle lower : List Bool}
    (hMU : BoolListLe middle upper)
    (hLM : BoolListLe lower middle) :
    relativeBoundaryFlagsList
        (relativeBoundaryFlagsList upper middle)
        (relativeBoundaryFlagsList upper lower) =
      relativeBoundaryFlagsList middle lower := by
  induction upper generalizing middle lower with
  | nil =>
      cases middle with
      | nil =>
          cases lower with
          | nil => rfl
          | cons l ls => simp [BoolListLe] at hLM
      | cons m ms => simp [BoolListLe] at hMU
  | cons u us ih =>
      cases middle with
      | nil => simp [BoolListLe] at hMU
      | cons m ms =>
          cases lower with
          | nil => simp [BoolListLe] at hLM
          | cons l ls =>
              simp only [BoolListLe] at hMU hLM
              have hTail := ih hMU.2 hLM.2
              cases u <;> cases m <;> cases l <;>
                simp_all [relativeBoundaryFlagsList]

/-- pattern level の relative flags inclusion。 -/
theorem relativeBoundaryFlags_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S T : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (hTS : T.Le S) :
    BoolListLe
      (relativeBoundaryFlags R T)
      (relativeBoundaryFlags R S) := by
  unfold relativeBoundaryFlags
  exact relativeBoundaryFlagsList_le
    (retainedFlags_le hSR)
    (retainedFlags_le hTS)

/-- pattern level の relative flags composition。 -/
theorem relativeBoundaryFlags_comp
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S T : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (hTS : T.Le S) :
    relativeBoundaryFlagsList
        (relativeBoundaryFlags R S)
        (relativeBoundaryFlags R T) =
      relativeBoundaryFlags S T := by
  unfold relativeBoundaryFlags
  exact relativeBoundaryFlagsList_comp
    (retainedFlags_le hSR)
    (retainedFlags_le hTS)

/-! ## 2. pure area-vector coarsening の relative composition -/

namespace LocalAreaTuple

/-- canonical area-vector coarsening は nonempty source を nonempty に保つ。 -/
theorem canonicalCoarsenValues_nonempty
    {xs : List ℕ}
    (hxs : xs ≠ [])
    (flags : List Bool) :
    canonicalCoarsenValues xs flags ≠ [] := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x rest =>
      cases rest with
      | nil => simp [canonicalCoarsenValues]
      | cons y ys =>
          cases flags with
          | nil => simp [canonicalCoarsenValues]
          | cons b bs =>
              cases b
              · cases h :
                  canonicalCoarsenValues (y :: ys) bs <;>
                  simp [canonicalCoarsenValues, flattenHeadAreaValues, h]
              · simp only [canonicalCoarsenValues, ne_eq, reduceCtorEq, not_false_eq_true]

/--
先頭 value を既に flat 0 にした後で valid Bool coarsening しても、
先に coarsening してから先頭を flat にしても一致する。
-/
theorem canonicalCoarsenValues_flattenHead
    {xs : List ℕ}
    (hxs : xs ≠ [])
    (flags : List Bool)
    (hFlags : flags.length = xs.length - 1) :
    canonicalCoarsenValues
        (flattenHeadAreaValues xs) flags =
      flattenHeadAreaValues
        (canonicalCoarsenValues xs flags) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x rest =>
      cases rest with
      | nil =>
          have hNil : flags = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using hFlags
          subst flags
          rfl
      | cons y ys =>
          cases flags with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hFlags
              omega
          | cons b bs =>
              cases b with
              | true =>
                  rfl
              | false =>
                  simp only [
                    flattenHeadAreaValues,
                    canonicalCoarsenValues
                  ]
                  exact (flattenHeadAreaValues_idem _).symm

/--
先頭の upper flag が `true` の場合の relative coarsening composition。

この場合は先頭 area が保持されるので、
tail 上の composition をそのまま先頭へ持ち上げられる。
-/
private theorem relativeBoundaryFlagsValues_spec_true_head
    (a b : ℕ)
    (tail : List ℕ)
    (us ls : List Bool)
    (lb : Bool)
    (hQLen :
      (relativeBoundaryFlagsList us ls).length =
        (canonicalCoarsenValues (b :: tail) us).length - 1)
    (hQComp :
      canonicalCoarsenValues
          (canonicalCoarsenValues (b :: tail) us)
          (relativeBoundaryFlagsList us ls) =
        canonicalCoarsenValues (b :: tail) ls) :
    let q :=
      relativeBoundaryFlagsList
        (true :: us) (lb :: ls)
    q.length =
        (canonicalCoarsenValues
          (a :: b :: tail) (true :: us)).length - 1 ∧
      canonicalCoarsenValues
          (canonicalCoarsenValues
            (a :: b :: tail) (true :: us))
          q =
        canonicalCoarsenValues
          (a :: b :: tail) (lb :: ls) := by
  have hUpperTailNe :
      canonicalCoarsenValues (b :: tail) us ≠ [] :=
    canonicalCoarsenValues_nonempty (by simp) us
  have hUpperTailPos :
      0 < (canonicalCoarsenValues (b :: tail) us).length :=
    List.length_pos_iff.mpr hUpperTailNe
  cases lb with
  | false =>
      constructor
      · change
          (false :: relativeBoundaryFlagsList us ls).length =
            (a :: canonicalCoarsenValues (b :: tail) us).length - 1
        simp only [List.length_cons]
        omega
      · change
          canonicalCoarsenValues
              (a :: canonicalCoarsenValues (b :: tail) us)
              (false :: relativeBoundaryFlagsList us ls) =
            flattenHeadAreaValues
              (canonicalCoarsenValues (b :: tail) ls)
        cases hU : canonicalCoarsenValues (b :: tail) us with
        | nil =>
            exact (hUpperTailNe hU).elim
        | cons x xs =>
            rw [hU] at hQComp
            simp only [canonicalCoarsenValues]
            rw [hQComp]
  | true =>
      constructor
      · change
          (true :: relativeBoundaryFlagsList us ls).length =
            (a :: canonicalCoarsenValues (b :: tail) us).length - 1
        simp only [List.length_cons]
        omega
      · change
          canonicalCoarsenValues
              (a :: canonicalCoarsenValues (b :: tail) us)
              (true :: relativeBoundaryFlagsList us ls) =
            a :: canonicalCoarsenValues (b :: tail) ls
        cases hU : canonicalCoarsenValues (b :: tail) us with
        | nil =>
            exact (hUpperTailNe hU).elim
        | cons x xs =>
            rw [hU] at hQComp
            simp only [canonicalCoarsenValues]
            rw [hQComp]

/--
先頭の upper/lower flag がともに `false` の場合の
relative coarsening composition。

先頭 coarsening は双方とも `flattenHeadAreaValues` になるので、
tail 上の composition と flatten/coarsening の交換則へ帰着する。
-/
private theorem relativeBoundaryFlagsValues_spec_false_head
    (a b : ℕ)
    (tail : List ℕ)
    (us ls : List Bool)
    (hQLen :
      (relativeBoundaryFlagsList us ls).length =
        (canonicalCoarsenValues (b :: tail) us).length - 1)
    (hQComp :
      canonicalCoarsenValues
          (canonicalCoarsenValues (b :: tail) us)
          (relativeBoundaryFlagsList us ls) =
        canonicalCoarsenValues (b :: tail) ls) :
    let q :=
      relativeBoundaryFlagsList
        (false :: us) (false :: ls)
    q.length =
        (canonicalCoarsenValues
          (a :: b :: tail) (false :: us)).length - 1 ∧
      canonicalCoarsenValues
          (canonicalCoarsenValues
            (a :: b :: tail) (false :: us))
          q =
        canonicalCoarsenValues
          (a :: b :: tail) (false :: ls) := by
  have hUpperTailNe :
      canonicalCoarsenValues (b :: tail) us ≠ [] :=
    canonicalCoarsenValues_nonempty (by simp) us
  constructor
  · change
      (relativeBoundaryFlagsList us ls).length =
        (flattenHeadAreaValues
          (canonicalCoarsenValues (b :: tail) us)).length - 1
    cases hU : canonicalCoarsenValues (b :: tail) us with
    | nil =>
        exact (hUpperTailNe hU).elim
    | cons x xs =>
        simp only [flattenHeadAreaValues, List.length_cons]
        rw [hU] at hQLen
        simpa using hQLen
  · change
      canonicalCoarsenValues
          (flattenHeadAreaValues
            (canonicalCoarsenValues (b :: tail) us))
          (relativeBoundaryFlagsList us ls) =
        flattenHeadAreaValues
          (canonicalCoarsenValues (b :: tail) ls)
    rw [
      canonicalCoarsenValues_flattenHead
        hUpperTailNe
        (relativeBoundaryFlagsList us ls)
        hQLen
    ]
    rw [hQComp]

/--
**## Pure Relative Coarsening Composition**

area-vector levelでも relative flags は length coarsening と同じ exact composition を持つ。
同時に relative flag count が current coarse area-vector の内部境界数に一致する。
-/
theorem relativeBoundaryFlagsValues_spec
    (values : List ℕ)
    (upper lower : List Bool)
    (hUpper : upper.length = values.length - 1)
    (hLower : lower.length = values.length - 1)
    (hLe : BoolListLe lower upper) :
    let q := relativeBoundaryFlagsList upper lower
    q.length =
        (canonicalCoarsenValues values upper).length - 1 ∧
      canonicalCoarsenValues
          (canonicalCoarsenValues values upper) q =
        canonicalCoarsenValues values lower := by
  induction values generalizing upper lower with
  | nil =>
      have hU : upper = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hUpper
      have hL : lower = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hLower
      subst upper
      subst lower
      simp [relativeBoundaryFlagsList, canonicalCoarsenValues]
  | cons a rest ih =>
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
          simp [relativeBoundaryFlagsList, canonicalCoarsenValues]
      | cons b tail =>
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
                        (b :: tail).length - 1 := by
                    simp only [List.length_cons] at hUpper ⊢
                    omega
                  have hLs :
                      ls.length =
                        (b :: tail).length - 1 := by
                    simp only [List.length_cons] at hLower ⊢
                    omega
                  simp only [BoolListLe] at hLe
                  have hIH :=
                    ih us ls hUs hLs hLe.2
                  have hQLen :
                      (relativeBoundaryFlagsList us ls).length =
                        (canonicalCoarsenValues
                          (b :: tail) us).length - 1 :=
                    hIH.1
                  have hQComp :
                      canonicalCoarsenValues
                          (canonicalCoarsenValues
                            (b :: tail) us)
                          (relativeBoundaryFlagsList us ls) =
                        canonicalCoarsenValues
                          (b :: tail) ls :=
                    hIH.2
                  cases ub with
                  | true =>
                      exact
                        relativeBoundaryFlagsValues_spec_true_head
                          a b tail us ls lb
                          hQLen hQComp
                  | false =>
                      cases lb with
                      | false =>
                          exact
                            relativeBoundaryFlagsValues_spec_false_head
                              a b tail us ls
                              hQLen hQComp
                      | true =>
                          have hBad : false = true :=
                            hLe.1 rfl
                          simp at hBad

/-- all-true valid flags leave the area vector unchanged。 -/
theorem canonicalCoarsenValues_replicate_true
    (values : List ℕ) :
    canonicalCoarsenValues
        values (List.replicate (values.length - 1) true) =
      values := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
      cases rest with
      | nil => rfl
      | cons b tail =>
          simp only [
            List.length_cons,
            Nat.succ_sub_one,
            List.replicate_succ,
            canonicalCoarsenValues
          ]
          simp only [
            List.length_cons,
            Nat.succ_sub_one
          ] at ih
          rw [ih]

end LocalAreaTuple

/-! ## 3. identity と transitivity -/

/-- all-true flags は length skeleton を変えない。 -/
theorem coarsenByFlags_replicate_true
    (rs : List ℕ) :
    coarsenByFlags
        rs (List.replicate (rs.length - 1) true) = rs := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
      cases rest with
      | nil => rfl
      | cons s tail =>
          simp only [
            List.length_cons,
            Nat.succ_sub_one,
            List.replicate_succ,
            coarsenByFlags
          ]
          simp only [
            List.length_cons,
            Nat.succ_sub_one
          ] at ih
          rw [ih]

/-- self-relative flags は current coarse skeleton の all-true flags。 -/
theorem relativeBoundaryFlags_self
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    relativeBoundaryFlags R R =
      List.replicate ((coarsenedLengthsFor D R).length - 1) true := by
  let L := coarsenedLengthsFor D R
  let q := relativeBoundaryFlags R R
  have hSpec := relativeBoundaryFlags_spec D
    (RetainedBoundaryPattern.le_refl R)
  have hQ : q.length = L.length - 1 := by
    simpa [q, L] using hSpec.1
  have hCoarseQ : coarsenByFlags L q = L := by
    simpa [q, L] using hSpec.2
  have hAllLen :
      (List.replicate (L.length - 1) true).length = L.length - 1 := by
    simp
  have hAllCoarse :
      coarsenByFlags L (List.replicate (L.length - 1) true) = L :=
    coarsenByFlags_replicate_true L
  have hEq : q = List.replicate (L.length - 1) true := by
    apply coarsenByFlags_injective
      hQ hAllLen
    · exact hCoarseQ.trans hAllCoarse.symm
    · exact coarsenedLengthsFor_pos D R
  simpa [q, L] using hEq

/--
canonical abstract inter-fiber coarsening の identity law。

同じ retained-boundary pattern `R` への transport では
relative boundary flags はすべて保持となるため、
area fiber point は exact に不変である。

この法則は `D` と Boolean boundary data のみに依存し、
`ContractingExponentPair` や primitive / reduced data、
actual source point には依存しない。
-/
theorem boundaryDecorationCanonicalInterfiberCoarsening_refl
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (A : BoundaryDecorationFiber D R) :
    boundaryDecorationCanonicalInterfiberCoarsening
        D (RetainedBoundaryPattern.le_refl R) A = A := by
  apply LocalAreaTuple.eq_of_values_eq
  rw [boundaryDecorationCanonicalInterfiberCoarsening_values]
  rw [relativeBoundaryFlags_self D R]
  have hLen := A.values_length
  rw [← hLen]
  exact
    LocalAreaTuple.canonicalCoarsenValues_replicate_true A.values

/--
## Canonical Interfiber Composition

`T ≤ S ≤ R` に対して、
`R → S → T` と二段階に行う canonical abstract transport は、
`R → T` の direct canonical transport と exact に一致する。

これは relative boundary flags の composition law と
pure recursive area-vector coarsening の composition law による。

従って nested downward transport の endpoint は経路の分割に依存せず、
この法則も `D` と Boolean boundary data のみから定まる。
-/
theorem boundaryDecorationCanonicalInterfiberCoarsening_trans
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S T : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (hTS : T.Le S)
    (A : BoundaryDecorationFiber D R) :
    boundaryDecorationCanonicalInterfiberCoarsening
        D hTS
        (boundaryDecorationCanonicalInterfiberCoarsening
          D hSR A) =
      boundaryDecorationCanonicalInterfiberCoarsening
        D (RetainedBoundaryPattern.le_trans hTS hSR) A := by
  apply LocalAreaTuple.eq_of_values_eq
  let qRS := relativeBoundaryFlags R S
  let qRT := relativeBoundaryFlags R T
  let qST := relativeBoundaryFlags S T
  have hQLe : BoolListLe qRT qRS := by
    simpa [qRS, qRT] using
      relativeBoundaryFlags_le hSR hTS
  have hQComp :
      relativeBoundaryFlagsList qRS qRT = qST := by
    simpa [qRS, qRT, qST] using
      relativeBoundaryFlags_comp hSR hTS
  have hRSlen :
      qRS.length = A.values.length - 1 := by
    have h := (relativeBoundaryFlags_spec D hSR).1
    rw [A.values_length]
    simpa [qRS] using h
  have hRTlen :
      qRT.length = A.values.length - 1 := by
    have h :=
      (relativeBoundaryFlags_spec D
        (RetainedBoundaryPattern.le_trans hTS hSR)).1
    rw [A.values_length]
    simpa [qRT] using h
  have hCore :=
    (LocalAreaTuple.relativeBoundaryFlagsValues_spec
      A.values qRS qRT hRSlen hRTlen hQLe).2
  rw [hQComp] at hCore
  calc
    (boundaryDecorationCanonicalInterfiberCoarsening
        D hTS
        (boundaryDecorationCanonicalInterfiberCoarsening
          D hSR A)).values
        =
      LocalAreaTuple.canonicalCoarsenValues
        (boundaryDecorationCanonicalInterfiberCoarsening
          D hSR A).values qST := by
          simpa [qST] using
            boundaryDecorationCanonicalInterfiberCoarsening_values
              D hTS
              (boundaryDecorationCanonicalInterfiberCoarsening
                D hSR A)
    _ =
      LocalAreaTuple.canonicalCoarsenValues
        (LocalAreaTuple.canonicalCoarsenValues
          A.values qRS) qST := by
          rw [boundaryDecorationCanonicalInterfiberCoarsening_values]
    _ =
      LocalAreaTuple.canonicalCoarsenValues
        A.values qRT := hCore
    _ =
      (boundaryDecorationCanonicalInterfiberCoarsening
        D
        (RetainedBoundaryPattern.le_trans hTS hSR)
        A).values := by
          symm
          simpa [qRT] using
            boundaryDecorationCanonicalInterfiberCoarsening_values
              D
              (RetainedBoundaryPattern.le_trans hTS hSR)
              A

/--
canonical abstract transport の composition law は、
actual fiber realizationへ transport した後にも exact に保存される。

すなわち `R → S → T` の二段階 actual canonical transport と
`R → T` の direct actual canonical transport は同じ endpoint を与える。

証明は target fiber equivalence の injectivity により
pure abstract composition law へ帰着する。
-/
theorem boundaryDecorationActualCanonicalInterfiberCoarsening_trans
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S T : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (hTS : T.Le S)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    boundaryDecorationActualCanonicalInterfiberCoarsening
        P hPrimitive hReduced u D hTS
        (boundaryDecorationActualCanonicalInterfiberCoarsening
          P hPrimitive hReduced u D hSR X) =
      boundaryDecorationActualCanonicalInterfiberCoarsening
        P hPrimitive hReduced u D
        (RetainedBoundaryPattern.le_trans hTS hSR) X := by
  apply (boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D T).injective
  rw [boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate]
  rw [boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate]
  rw [boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate]
  exact boundaryDecorationCanonicalInterfiberCoarsening_trans
    D hSR hTS
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R X)

/-! ## 4. Boolean diamond と closure -/

/--
異なる二つの retained boundary をどちらの順序で削除しても、
Boolean base level の target pattern は exact に一致する。

これは fiber coordinate や actual realization に依存しない
pure Boolean-base diamond law。
-/
theorem boundaryDecorationCanonicalInterfiberMerge_base_comm
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (a b : InternalRecordBoundary D) :
    eraseRetainedBoundary (eraseRetainedBoundary R a) b =
      eraseRetainedBoundary (eraseRetainedBoundary R b) a :=
  eraseRetainedBoundary_comm R a b

/--
canonical abstract inter-fiber coarsening の coherence closure data。

identity と composition により、任意の nested downward canonical transport は
同じ endpoint への direct transport に exact に潰せる。

さらに Boolean base の one-boundary deletion squares は可換である。

したがってこの package は canonical fiber dynamics の coherence を
actual realization より前の pure abstract layer だけで閉じている。
`ContractingExponentPair` や primitive / reduced data には依存しない。
-/
structure BoundaryDecorationInterfiberMergeCoherenceClosed
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : Prop where

  identity :
    ∀ (R : RetainedBoundaryPattern D)
      (A : BoundaryDecorationFiber D R),
      boundaryDecorationCanonicalInterfiberCoarsening
          D
          (RetainedBoundaryPattern.le_refl R) A = A

  composition :
    ∀ {R S T : RetainedBoundaryPattern D}
      (hSR : S.Le R)
      (hTS : T.Le S)
      (A : BoundaryDecorationFiber D R),
      boundaryDecorationCanonicalInterfiberCoarsening
          D hTS
          (boundaryDecorationCanonicalInterfiberCoarsening
            D hSR A) =
        boundaryDecorationCanonicalInterfiberCoarsening
          D
          (RetainedBoundaryPattern.le_trans hTS hSR) A

  base_diamond :
    ∀ (R : RetainedBoundaryPattern D)
      (a b : InternalRecordBoundary D),
      eraseRetainedBoundary
          (eraseRetainedBoundary R a) b =
        eraseRetainedBoundary
          (eraseRetainedBoundary R b) a

/--
canonical inter-fiber merge coherence closure theorem。

pure abstract coarsening の identity law と composition law、
および Boolean base の one-boundary diamond law を同時に確立する。

従って canonical downward fiber transport の coherence は、
actual arithmetic realizationを導入する前の段階ですでに閉じている。
-/
theorem boundaryDecorationInterfiberMergeCoherence_closed
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    BoundaryDecorationInterfiberMergeCoherenceClosed D := by
  refine {
    identity := ?_
    composition := ?_
    base_diamond := ?_
  }
  · intro R A
    exact boundaryDecorationCanonicalInterfiberCoarsening_refl
      D R A
  · intro R S T hSR hTS A
    exact boundaryDecorationCanonicalInterfiberCoarsening_trans
      D hSR hTS A
  · intro R a b
    exact eraseRetainedBoundary_comm R a b

end RecordFerrers
end Collatz2
