import CollatzLean.Collatz2.RecordFerrers.Perturbation.P28CanonicalCoarseningNormalization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-!
# Record–Ferrers 摂動理論 29: 標準境界の Boolean 粗視化

P28 では、一つの連続 Record 区間を一つへまとめる粗視化を、
全体の `RecordDecomposition` へ貼り戻せることを示した。

本ファイルでは cut 1 からの標準分解

  [r₁, r₂, ..., rₘ]

にある `m-1` 個の内部 Record 境界を、残すか消すかで指定する。
純粋な境界選択の型は Boolean 立方体であり、その大きさは exact に `2^(m-1)`。

さらに、境界選択から得る長さ列を定義し、異なる選択が異なる長さ列を与えることを示す。
最後に P28 の actual 粗視化を再帰して、全ての境界選択が同じ fixed chord 内の
FirstCrossing `FiberPoint` として実現できることを示す。

注意: ここで Boolean 格子と呼ぶのは「標準境界の選択・粗視化」の格子である。
既存 Ferrers lattice の meet / join に閉じた部分格子であるとは主張しない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 内部 Record 境界と保持 pattern -/

/--
cut 1 からの標準分解にある内部 Record 境界の番号。
`m` blocks なら `Fin (m-1)`。
-/
def InternalRecordBoundary
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : Type :=
  Fin (D.lengths.length - 1)

/-- 内部 Record 境界には判定可能な等号がある。 -/
instance instDecidableEqInternalRecordBoundary
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    DecidableEq (InternalRecordBoundary D) := by
  unfold InternalRecordBoundary
  infer_instance

/-- 各内部 Record 境界を残すか消すかを Bool で指定する。 -/
def RetainedBoundaryPattern
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : Type :=
  InternalRecordBoundary D → Bool

/-- 全内部境界を残す pattern。 -/
def retainAllBoundaries
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : RetainedBoundaryPattern D :=
  fun _ => true

/-- 全内部境界を消す pattern。 -/
def retainNoBoundaries
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : RetainedBoundaryPattern D :=
  fun _ => false

/-- 一つの内部境界だけを消し、他は全て残す。 -/
def deleteOneBoundary
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (b : InternalRecordBoundary D) : RetainedBoundaryPattern D :=
  fun j => if j = b then false else true

/-- 保持 pattern の包含順序。`R ≤ S` は R で残す境界を S でも残すこと。 -/
def RetainedBoundaryPattern.Le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) : Prop :=
  ∀ i, R i = true → S i = true

/-- Boolean meet: 両方で残す境界だけを残す。 -/
def retainedMeet
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) : RetainedBoundaryPattern D :=
  fun i => R i && S i

/-- Boolean join: どちらかで残す境界を残す。 -/
def retainedJoin
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) : RetainedBoundaryPattern D :=
  fun i => R i || S i

/-- Boolean complement。 -/
def retainedComplement
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) : RetainedBoundaryPattern D :=
  fun i => !(R i)

@[simp] theorem retainedMeet_complement
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) :
    retainedMeet R (retainedComplement R) = retainNoBoundaries D := by
  funext i
  cases h : R i <;>
    simp [retainedMeet, retainedComplement, retainNoBoundaries, h]

@[simp] theorem retainedJoin_complement
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) :
    retainedJoin R (retainedComplement R) = retainAllBoundaries D := by
  funext i
  cases h : R i <;>
    simp [retainedJoin, retainedComplement, retainAllBoundaries, h]

@[simp] theorem retainedMeet_comm
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    retainedMeet R S = retainedMeet S R := by
  funext i
  cases hR : R i <;> cases hS : S i <;>
    simp [retainedMeet, hR, hS]

@[simp] theorem retainedJoin_comm
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    retainedJoin R S = retainedJoin S R := by
  funext i
  cases hR : R i <;> cases hS : S i <;>
    simp [retainedJoin, hR, hS]

/-- 内部 Record 境界は有限型。 -/
instance instFintypeInternalRecordBoundary
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    Fintype (InternalRecordBoundary D) := by
  unfold InternalRecordBoundary
  infer_instance

/-- 境界保持 pattern 全体も有限型。 -/
instance instFintypeRetainedBoundaryPattern
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    Fintype (RetainedBoundaryPattern D) := by
  unfold RetainedBoundaryPattern
  infer_instance

/--
内部境界が `m-1` 個なので保持 pattern は exact に `2^(m-1)` 個。
-/
theorem retainedBoundaryPattern_card
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    Fintype.card (RetainedBoundaryPattern D) =
      2 ^ (D.lengths.length - 1) := by
  unfold RetainedBoundaryPattern
  rw [Fintype.card_fun]
  simp [InternalRecordBoundary]

/-! ## 2. pattern から粗視化長さ列を作る -/

/-- 先頭 block length を、後ろの最初の block へ吸収する。 -/
def mergeHeadLength (r : ℕ) : List ℕ → List ℕ
  | [] => [r]
  | s :: rest => (r + s) :: rest

/--
Bool 列に従って隣接境界を残す / 消す。
`true` は境界を残し、`false` は左右 block を足し合わせる。
有効な利用では Bool 列の長さは `lengths.length - 1`。
-/
def coarsenByFlags : List ℕ → List Bool → List ℕ
  | [], _ => []
  | [r], _ => [r]
  | r :: s :: rest, [] => r :: s :: rest
  | r :: s :: rest, b :: bs =>
      match b with
      | true => r :: coarsenByFlags (s :: rest) bs
      | false => mergeHeadLength r (coarsenByFlags (s :: rest) bs)

/-- pattern を Bool 列へ読む。 -/
def retainedFlags
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) : List Bool :=
  List.ofFn R

@[simp] theorem retainedFlags_length
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) :
    (retainedFlags R).length = D.lengths.length - 1 := by
  unfold retainedFlags
  change
    (List.ofFn
      (fun i : Fin (D.lengths.length - 1) => R i)).length =
      D.lengths.length - 1
  exact List.length_ofFn


/-- source decomposition と保持 pattern から定まる粗視化長さ列。 -/
def coarsenedLengthsFor
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : List ℕ :=
  coarsenByFlags D.lengths (retainedFlags R)

/-- `mergeHeadLength` は nonempty list 上で injective。 -/
theorem mergeHeadLength_injective_of_nonempty
    (r : ℕ)
    {xs ys : List ℕ}
    (hx : xs ≠ [])
    (hy : ys ≠ [])
    (hEq : mergeHeadLength r xs = mergeHeadLength r ys) :
    xs = ys := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xt =>
      cases ys with
      | nil => exact (hy rfl).elim
      | cons y yt =>
          simp only [mergeHeadLength, List.cons.injEq] at hEq
          rcases hEq with ⟨hHead, hTail⟩
          have hxy : x = y := by omega
          subst y
          rw [hTail]

/-- cons source はどの Bool 列で粗視化しても nonempty。 -/
theorem coarsenByFlags_cons_ne_nil
    (r : ℕ)
    (rest : List ℕ)
    (flags : List Bool) :
    coarsenByFlags (r :: rest) flags ≠ [] := by
  induction rest generalizing r flags with
  | nil =>
      simp [coarsenByFlags]
  | cons s tail ih =>
      cases flags with
      | nil => simp [coarsenByFlags]
      | cons b bs =>
          cases b with
          | true => simp [coarsenByFlags]
          | false =>
              have hTail : coarsenByFlags (s :: tail) bs ≠ [] :=
                ih s bs
              cases hC : coarsenByFlags (s :: tail) bs with
              | nil => exact (hTail hC).elim
              | cons t ts => simp [coarsenByFlags, hC, mergeHeadLength]

/-- nonempty source は粗視化後も nonempty。 -/
theorem coarsenByFlags_nonempty
    {rs : List ℕ}
    (hrs : rs ≠ [])
    (flags : List Bool) :
    coarsenByFlags rs flags ≠ [] := by
  cases rs with
  | nil => exact (hrs rfl).elim
  | cons r rest => exact coarsenByFlags_cons_ne_nil r rest flags

/-- nonempty tail では `true` は先頭境界をそのまま残す。 -/
theorem coarsenByFlags_cons_true
    (r : ℕ)
    {rest : List ℕ}
    (hRest : rest ≠ [])
    (flags : List Bool) :
    coarsenByFlags (r :: rest) (true :: flags) =
      r :: coarsenByFlags rest flags := by
  cases rest with
  | nil => exact (hRest rfl).elim
  | cons s tail => rfl

/-- nonempty tail では `false` は先頭境界を消して先頭 block を吸収する。 -/
theorem coarsenByFlags_cons_false
    (r : ℕ)
    {rest : List ℕ}
    (hRest : rest ≠ [])
    (flags : List Bool) :
    coarsenByFlags (r :: rest) (false :: flags) =
      mergeHeadLength r (coarsenByFlags rest flags) := by
  cases rest with
  | nil => exact (hRest rfl).elim
  | cons s tail => rfl

/-- positive source lengths は粗視化後も全て positive。 -/
theorem coarsenByFlags_all_pos
    {rs : List ℕ}
    (flags : List Bool)
    (hPos : ∀ r ∈ rs, 0 < r) :
    ∀ r ∈ coarsenByFlags rs flags, 0 < r := by
  revert hPos
  induction rs generalizing flags with
  | nil =>
      intro hPos r hr
      simp [coarsenByFlags] at hr
  | cons r rest ih =>
      intro hPos
      have hrPos : 0 < r := hPos r (by simp)
      have hRest : ∀ x ∈ rest, 0 < x := by
        intro x hx
        exact hPos x (by simp [hx])
      cases rest with
      | nil =>
          intro x hx
          simp only [coarsenByFlags, List.mem_cons, List.not_mem_nil, or_false] at hx
          subst x
          exact hrPos
      | cons s tail =>
          cases flags with
          | nil =>
              simpa [coarsenByFlags] using hPos
          | cons b bs =>
              cases b with
              | true =>
                  intro x hx
                  simp only [coarsenByFlags, List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · exact hrPos
                  · exact ih bs hRest x hx
              | false =>
                  have hTailPos := ih bs hRest
                  have hTailNe : coarsenByFlags (s :: tail) bs ≠ [] :=
                    coarsenByFlags_nonempty (by simp) bs
                  cases hC : coarsenByFlags (s :: tail) bs with
                  | nil => exact (hTailNe hC).elim
                  | cons t ts =>
                      intro x hx
                      have htPos : 0 < t := by
                        exact hTailPos t (by rw [hC]; simp)
                      simp only [coarsenByFlags, hC, mergeHeadLength,
                        List.mem_cons] at hx
                      rcases hx with rfl | hx
                      · omega
                      · exact hTailPos x (by rw [hC]; simp [hx])

/--
positive source lengths では、同じ source に対する Bool 境界列は
粗視化長さ列から一意に復元できる。
-/
theorem coarsenByFlags_injective
    {rs : List ℕ}
    {f g : List Bool}
    (hf : f.length = rs.length - 1)
    (hg : g.length = rs.length - 1)
    (hEq : coarsenByFlags rs f = coarsenByFlags rs g)
    (hPos : ∀ r ∈ rs, 0 < r) :
    f = g := by
  revert hPos
  induction rs generalizing f g with
  | nil =>
      intro hPos
      have hf0 : f.length = 0 := by simpa using hf
      have hg0 : g.length = 0 := by simpa using hg
      exact
        (List.length_eq_zero_iff.mp hf0).trans
          (List.length_eq_zero_iff.mp hg0).symm
  | cons r rest ih =>
      intro hPos
      cases rest with
      | nil =>
          have hf0 : f.length = 0 := by simpa using hf
          have hg0 : g.length = 0 := by simpa using hg
          exact
            (List.length_eq_zero_iff.mp hf0).trans
              (List.length_eq_zero_iff.mp hg0).symm
      | cons s tail =>
          have hRestPos : ∀ x ∈ (s :: tail), 0 < x := by
            intro x hx
            exact hPos x (by simp [hx])
          cases f with
          | nil =>
              have : (s :: tail).length = 0 := by simpa using hf.symm
              simp at this
          | cons bf fs =>
              cases g with
              | nil =>
                  have : (s :: tail).length = 0 := by simpa using hg.symm
                  simp at this
              | cons bg gs =>
                  have hfs : fs.length = (s :: tail).length - 1 := by
                    simp only [List.length_cons] at hf ⊢
                    omega
                  have hgs : gs.length = (s :: tail).length - 1 := by
                    simp only [List.length_cons] at hg ⊢
                    omega
                  cases bf with
                  | true =>
                      cases bg with
                      | true =>
                          have hTailEq :
                              coarsenByFlags (s :: tail) fs =
                                coarsenByFlags (s :: tail) gs := by
                            simpa [coarsenByFlags] using hEq
                          have hfg := ih hfs hgs hTailEq hRestPos
                          rw [hfg]
                      | false =>
                          have hTailNe :
                              coarsenByFlags (s :: tail) gs ≠ [] :=
                            coarsenByFlags_nonempty (by simp) gs
                          cases hC : coarsenByFlags (s :: tail) gs with
                          | nil => exact (hTailNe hC).elim
                          | cons t ts =>
                              have htPos : 0 < t :=
                                coarsenByFlags_all_pos gs hRestPos t (by rw [hC]; simp)
                              have hHead : r = r + t := by
                                simpa [coarsenByFlags, hC, mergeHeadLength] using
                                  congrArg List.head? hEq
                              omega
                  | false =>
                      cases bg with
                      | true =>
                          have hTailNe :
                              coarsenByFlags (s :: tail) fs ≠ [] :=
                            coarsenByFlags_nonempty (by simp) fs
                          cases hC : coarsenByFlags (s :: tail) fs with
                          | nil => exact (hTailNe hC).elim
                          | cons t ts =>
                              have htPos : 0 < t :=
                                coarsenByFlags_all_pos fs hRestPos t (by rw [hC]; simp)
                              have hHead : r + t = r := by
                                simpa [coarsenByFlags, hC, mergeHeadLength] using
                                  congrArg List.head? hEq
                              omega
                      | false =>
                          have hA : coarsenByFlags (s :: tail) fs ≠ [] :=
                            coarsenByFlags_nonempty (by simp) fs
                          have hB : coarsenByFlags (s :: tail) gs ≠ [] :=
                            coarsenByFlags_nonempty (by simp) gs
                          have hMergeEq :
                              mergeHeadLength r (coarsenByFlags (s :: tail) fs) =
                                mergeHeadLength r (coarsenByFlags (s :: tail) gs) := by
                            simpa [coarsenByFlags] using hEq
                          have hTailEq :=
                            mergeHeadLength_injective_of_nonempty r hA hB hMergeEq
                          have hfg := ih hfs hgs hTailEq hRestPos
                          rw [hfg]

/-- 保持 pattern から粗視化長さ列への写像は injective。 -/
theorem coarsenedLengthsFor_injective
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    Function.Injective (coarsenedLengthsFor D) := by
  intro R S hEq
  have hFlags : retainedFlags R = retainedFlags S := by
    apply coarsenByFlags_injective
      (retainedFlags_length R)
      (retainedFlags_length S)
      hEq
    exact D.lengths_pos
  exact List.ofFn_injective hFlags

/-- pattern によって得られる長さ列だけを集めた型。 -/
def CoarsenedLengthList
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : Type :=
  { L : List ℕ // ∃ R : RetainedBoundaryPattern D, coarsenedLengthsFor D R = L }

/--
保持 pattern と、そこから得る粗視化長さ列は exact に一対一対応する。
-/
noncomputable def retainedPatternEquivCoarsenedLengthList
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    RetainedBoundaryPattern D ≃ CoarsenedLengthList D where
  toFun := fun R => ⟨coarsenedLengthsFor D R, ⟨R, rfl⟩⟩
  invFun := fun L => Classical.choose L.property
  left_inv := by
    intro R
    let L : CoarsenedLengthList D :=
      ⟨coarsenedLengthsFor D R, ⟨R, rfl⟩⟩
    change Classical.choose L.property = R
    apply coarsenedLengthsFor_injective D
    exact Classical.choose_spec L.property
  right_inv := by
    intro L
    apply Subtype.ext
    exact Classical.choose_spec L.property

/-! ## 3. Boolean 粗視化の exact count -/

/--
粗視化長さ列は保持 pattern と一対一なので、組合せ論的には
Boolean 立方体 `B_(m-1)` と同じ大きさを持つ。
-/
theorem booleanCoarsening_exact_count
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    Fintype.card (RetainedBoundaryPattern D) =
      2 ^ (D.lengths.length - 1) :=
  retainedBoundaryPattern_card D

/-! ## 4–5. P28 actual 粗視化の反復 -/

/--
再帰証明で必要な左側一致データ。
source と target が `stop` 以前で height / rank を共有することを保持する。
-/
def LeftAgreement
    {p H : ℕ}
    (u v : FiberPoint p H)
    (stop : ℕ) : Prop :=
  (∀ k : ℕ, k ≤ stop → u.height k = v.height k) ∧
    (∀ k : ℕ, k ≤ stop →
      chordRankInt v.word k = chordRankInt u.word k)

/--
RecordChain と有効な Bool 境界列から、対応する actual 粗視化 chain を構成する。
`false` の最初の境界を消す箇所では P28 の direct coarsening を使う。
-/
theorem RecordChain.exists_actual_coarsening_of_flags
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {u : FiberPoint P.oddCount P.twoDepth}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hFu : FirstCrossing u.word)
    (flags : List Bool)
    (hFlags : flags.length = lengths.length - 1) :
    0 < start →
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ out : List ℕ,
        RecordChain v start out ∧
        FirstCrossing v.word ∧
        out = coarsenByFlags lengths flags ∧
        LeftAgreement u v start := by
  induction C generalizing flags with
  | @last start len B hTerminal =>
      intro hStartPos
      have hFlags0 : flags.length = 0 := by simpa using hFlags
      have hNil : flags = [] := List.eq_nil_of_length_eq_zero hFlags0
      subst flags
      refine ⟨u, [len], RecordChain.last B hTerminal, hFu, ?_, ?_⟩
      · simp [coarsenByFlags]
      · constructor
        · intro k hk
          rfl
        · intro k hk
          rfl
  | @cons start len rest B hInterior T ih =>
      intro hStartPos
      have hRestNe : rest ≠ [] := T.nonempty
      cases flags with
      | nil =>
          have hRestLen0 : rest.length = 0 := by simpa using hFlags.symm
          exact (hRestNe (List.eq_nil_of_length_eq_zero hRestLen0)).elim
      | cons keep more =>
          have hMore : more.length = rest.length - 1 := by
            have hRestLenPos : 0 < rest.length :=
              List.length_pos_iff.mpr hRestNe
            simp only [List.length_cons] at hFlags
            omega
          obtain ⟨v, tailOut, Ctail, hFv, hTailOut, hAgreeTail⟩ :=
            ih more hMore (by omega)
          have hBv : RecordBlock v start len := by
            apply recordBlock_preserved_of_equal_data B
            · intro j hj
              exact hAgreeTail.1 (start + j) (by omega)
            · intro j hj
              exact hAgreeTail.2 (start + j) (by omega)
          cases keep with
          | true =>
              let Cwhole : RecordChain v start (len :: tailOut) :=
                RecordChain.cons hBv hInterior Ctail
              refine ⟨v, len :: tailOut, Cwhole, hFv, ?_, ?_⟩
              · rw [coarsenByFlags_cons_true len hRestNe more]
                rw [← hTailOut]
              · constructor
                · intro k hk
                  exact hAgreeTail.1 k (by omega)
                · intro k hk
                  exact hAgreeTail.2 k (by omega)
          | false =>
              let Dv : RecordDecomposition v start := {
                lengths := len :: tailOut
                chain := RecordChain.cons hBv hInterior Ctail
                whole_firstCrossing := hFv
              }
              cases Ctail with
              | @last _ len2 B2 hTerminal2 =>
                  let W : TerminalCoarseningWindow Dv [] [len, len2] := {
                    cut := start
                    leftPart := RecordLeftSegment.empty
                    tailPart := by
                      exact RecordChain.cons hBv hInterior
                        (RecordChain.last B2 hTerminal2)
                    sourceLengths := by
                      dsimp [Dv]
                  }
                  obtain ⟨w, Ew, hRep, hEw, _hSource⟩ :=
                    directTerminalCoarsening
                      P hPrimitive hReduced v Dv W hStartPos
                  refine ⟨w, Ew.lengths, Ew.chain, Ew.whole_firstCrossing, ?_, ?_⟩
                  · have hTailSingle :
                        coarsenByFlags rest more = [len2] := by
                      simpa using hTailOut.symm
                    rw [hEw]
                    rw [coarsenByFlags_cons_false len hRestNe more]
                    rw [hTailSingle]
                    simp [mergeHeadLength]
                  · constructor
                    · intro k hk
                      calc
                        u.height k = v.height k := hAgreeTail.1 k (by omega)
                        _ = w.height k := hRep.height_eq_of_le_start hk
                    · intro k hk
                      calc
                        chordRankInt w.word k = chordRankInt v.word k :=
                          hRep.chordRankInt_outside
                            (by omega)
                            (Or.inl hk)
                        _ = chordRankInt u.word k :=
                          hAgreeTail.2 k (by omega)
              | @cons _ len2 rest2 B2 hInterior2 T2 =>
                  let Rmid :
                      InteriorRecordRun v start [len, len2] ((start + len) + len2) :=
                    InteriorRecordRun.cons hBv hInterior
                      (InteriorRecordRun.one B2 hInterior2)
                  let W : InteriorCoarseningWindow Dv [] [len, len2] rest2 := {
                    leftStop := start
                    middleStop := (start + len) + len2
                    leftPart := RecordLeftSegment.empty
                    middlePart := Rmid
                    rightPart := T2
                    sourceLengths := by
                      dsimp [Dv]
                  }
                  obtain ⟨w, Ew, hRep, hEw, _hSource⟩ :=
                    directInteriorCoarsening
                      P hPrimitive hReduced v Dv W
                  refine ⟨w, Ew.lengths, Ew.chain, Ew.whole_firstCrossing, ?_, ?_⟩
                  · have hTailCons :
                        coarsenByFlags rest more = len2 :: rest2 := by
                      simpa using hTailOut.symm
                    rw [hEw]
                    rw [coarsenByFlags_cons_false len hRestNe more]
                    rw [hTailCons]
                    simp [mergeHeadLength, coarsenedLengths]
                  · constructor
                    · intro k hk
                      calc
                        u.height k = v.height k := hAgreeTail.1 k (by omega)
                        _ = w.height k := hRep.height_eq_of_le_start hk
                    · intro k hk
                      calc
                        chordRankInt w.word k = chordRankInt v.word k :=
                          hRep.chordRankInt_outside
                            (by omega)
                            (Or.inl hk)
                        _ = chordRankInt u.word k :=
                          hAgreeTail.2 k (by omega)

/--
任意の保持 pattern は actual FirstCrossing target として実現できる。
-/
theorem exists_actual_realization_of_pattern
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ E : RecordDecomposition v 1,
        FirstCrossing v.word ∧
        E.lengths = coarsenedLengthsFor D R := by
  obtain ⟨v, out, C, hFv, hOut, _hAgree⟩ :=
    RecordChain.exists_actual_coarsening_of_flags
      P hPrimitive hReduced D.chain D.whole_firstCrossing
      (retainedFlags R) (retainedFlags_length R) (by omega)
  let E : RecordDecomposition v 1 := {
    lengths := out
    chain := C
    whole_firstCrossing := hFv
  }
  exact ⟨v, E, hFv, by simpa [E, coarsenedLengthsFor] using hOut⟩

/--
一つの内部境界だけを消す場合も P28 actual 粗視化として実現できる。
-/
theorem exists_actual_oneBoundaryDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (b : InternalRecordBoundary D) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ E : RecordDecomposition v 1,
        FirstCrossing v.word ∧
        E.lengths = coarsenedLengthsFor D (deleteOneBoundary D b) :=
  exists_actual_realization_of_pattern
    P hPrimitive hReduced u D (deleteOneBoundary D b)

/-- pattern の actual realization を bundle する。 -/
structure PatternRealization
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) where
  point : FiberPoint P.oddCount P.twoDepth
  decomposition : RecordDecomposition point 1
  lengths_eq : decomposition.lengths = coarsenedLengthsFor D R

/-- 任意 pattern は actual realization を持つ。 -/
theorem patternRealization_nonempty
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    Nonempty (PatternRealization P u D R) := by
  obtain ⟨v, E, _hFv, hE⟩ :=
    exists_actual_realization_of_pattern
      P hPrimitive hReduced u D R
  exact ⟨{
    point := v
    decomposition := E
    lengths_eq := hE
  }⟩

/-- 各 pattern から一つ actual realization を選ぶ。 -/
noncomputable def chosenPatternRealization
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    PatternRealization P u D R :=
  Classical.choice
    (patternRealization_nonempty
      P hPrimitive hReduced u D R)

/--
point が等しい二つの RecordDecomposition は、
同じ start なら length skeleton も一致する。
-/
theorem RecordDecomposition.lengths_unique_of_point_eq
    {p H : ℕ}
    {x y : FiberPoint p H}
    {start : ℕ}
    (hxy : x = y)
    (A : RecordDecomposition x start)
    (B : RecordDecomposition y start) :
    A.lengths = B.lengths := by
  subst y
  exact A.lengths_unique B

/-- 異なる保持 pattern は、選ばれた actual FiberPoint も異なる。 -/
theorem chosenPatternPoint_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    Function.Injective
      (fun R : RetainedBoundaryPattern D =>
        (chosenPatternRealization
          P hPrimitive hReduced u D R).point) := by
  intro R S hPoint
  let A :=
    chosenPatternRealization
      P hPrimitive hReduced u D R
  let B :=
    chosenPatternRealization
      P hPrimitive hReduced u D S
  change A.point = B.point at hPoint
  have hCanon :
      A.decomposition.lengths =
        B.decomposition.lengths := by
    exact
      RecordDecomposition.lengths_unique_of_point_eq
        hPoint A.decomposition B.decomposition
  have hLengths :
      coarsenedLengthsFor D R =
        coarsenedLengthsFor D S := by
    calc
      coarsenedLengthsFor D R
          = A.decomposition.lengths :=
        A.lengths_eq.symm
      _ = B.decomposition.lengths :=
        hCanon
      _ = coarsenedLengthsFor D S :=
        B.lengths_eq
  exact coarsenedLengthsFor_injective D hLengths

/--
## 主定理: Boolean 粗視化の全 pattern は相異なる actual FirstCrossing point として実現される

source が `m` blocks を持つなら domain は exact に `2^(m-1)` 個。
-/
theorem exists_boolean_family_of_actual_firstCrossing_points
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ∃ f : RetainedBoundaryPattern D →
        FiberPoint P.oddCount P.twoDepth,
      Function.Injective f ∧
      (∀ R : RetainedBoundaryPattern D,
        FirstCrossing (f R).word ∧
        ∃ E : RecordDecomposition (f R) 1,
          E.lengths = coarsenedLengthsFor D R) ∧
      Fintype.card (RetainedBoundaryPattern D) =
        2 ^ (D.lengths.length - 1) := by
  let f : RetainedBoundaryPattern D →
      FiberPoint P.oddCount P.twoDepth :=
    fun R =>
      (chosenPatternRealization
        P hPrimitive hReduced u D R).point
  refine ⟨f, ?_, ?_, retainedBoundaryPattern_card D⟩
  · exact chosenPatternPoint_injective
      P hPrimitive hReduced u D
  · intro R
    let A := chosenPatternRealization
      P hPrimitive hReduced u D R
    refine ⟨A.decomposition.whole_firstCrossing, ?_⟩
    exact ⟨A.decomposition, A.lengths_eq⟩

end RecordFerrers
end Collatz2
