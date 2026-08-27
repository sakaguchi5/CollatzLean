import CollatzLean.Collatz2.RecordFerrers.Perturbation.P34ActualCanonicalBoundaryDeletion
import Mathlib.Order.WellFounded

/-!
# Record–Ferrers 摂動理論 35: actual 境界削除系の有限閉包

P34 では一つの canonical internal boundary の削除を、標準平坦 FirstCrossing family 内の
strict downward `BlockReplacement` として actual に実現した。

本ファイルでは、この一段関係を有限書き換え系として閉じる。

* 保持境界の有限集合と個数を定義し、一段削除で個数が exact に 1 減ることを示す。
* 複数境界の削除を finite set で表し、削除集合の union が操作の合成そのものであることを示す。
* actual 一段削除の反射推移閉包を定義し、Boolean 順序 `S.Le R` と reachability が exact に同値であることを示す。
* 一段関係が well-founded であり、全消去 pattern だけが normal form であることを示す。
* 任意の pattern は全消去 pattern へ到達し、その FiberPoint は `canonicalNoBoundaryPoint` に exact に一致する。
* 任意の二つの削除経路は共通 descendant を持ち、削除順序によらず同じ canonical endpoint に到達する。

したがって P29--P35 の Boolean 粗視化 family は、有限・停止・合流的で一意な幾何学的 normal form を持つ
actual Record--Ferrers deformation system として閉じる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 保持境界集合と一段削除の測度 -/

/-- pattern `R` で実際に保持されている内部境界の有限集合。 -/
def retainedBoundarySet
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    Finset (InternalRecordBoundary D) := by
  letI : DecidablePred
      (fun b : InternalRecordBoundary D => R b = true) :=
    fun b => inferInstance
  exact Finset.univ.filter (fun b => R b = true)

@[simp] theorem mem_retainedBoundarySet
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    b ∈ retainedBoundarySet D R ↔ R b = true := by
  simp [retainedBoundarySet]

/-- pattern に残っている内部境界数。 -/
def retainedBoundaryCount
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : ℕ :=
  (retainedBoundarySet D R).card

/-- 一境界削除後の保持集合は、元の保持集合からその一点を erase したもの。 -/
theorem retainedBoundarySet_eraseRetainedBoundary
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    retainedBoundarySet D (eraseRetainedBoundary R b) =
      (retainedBoundarySet D R).erase b := by
  ext i
  simp only [
    retainedBoundarySet,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and,
    Finset.mem_erase
  ]
  by_cases hib : i = b
  · subst i
    simp [eraseRetainedBoundary]
  · simp [eraseRetainedBoundary, hib]

/-- 保持されている境界を一つ消すと、保持境界数は exact に 1 減る。 -/
theorem retainedBoundaryCount_erase_add_one
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    retainedBoundaryCount D (eraseRetainedBoundary R b) + 1 =
      retainedBoundaryCount D R := by
  unfold retainedBoundaryCount
  rw [retainedBoundarySet_eraseRetainedBoundary]
  apply Finset.card_erase_add_one
  exact (mem_retainedBoundarySet R b).2 hb

/-- canonical 一段削除は保持境界数を strict に下げる。 -/
theorem CanonicalBoundaryDeletion.count_lt
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S : RetainedBoundaryPattern D}
    (h : CanonicalBoundaryDeletion D R S) :
    retainedBoundaryCount D S < retainedBoundaryCount D R := by
  rcases h with ⟨b, hb, rfl⟩
  have hCount := retainedBoundaryCount_erase_add_one R b hb
  omega

/-- actual 一段削除も同じ測度を strict に下げる。 -/
theorem ActualCanonicalBoundaryDeletion.count_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (A : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S) :
    retainedBoundaryCount D S < retainedBoundaryCount D R :=
  CanonicalBoundaryDeletion.count_lt A.pattern_step

/-! ## 2. finite set による複数境界削除 -/

/-- finite set `E` に入った内部境界をまとめて消す。 -/
def eraseRetainedBoundaries
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (E : Finset (InternalRecordBoundary D)) :
    RetainedBoundaryPattern D :=
  fun b => if b ∈ E then false else R b

@[simp] theorem eraseRetainedBoundaries_empty
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) :
    eraseRetainedBoundaries R ∅ = R := by
  funext b
  simp [eraseRetainedBoundaries]

/-- singleton の finite-set 削除は P31 の一境界削除そのもの。 -/
theorem eraseRetainedBoundaries_singleton
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    eraseRetainedBoundaries R {b} = eraseRetainedBoundary R b := by
  funext i
  by_cases hib : i = b
  · subst i
    simp [eraseRetainedBoundaries, eraseRetainedBoundary]
  · simp [eraseRetainedBoundaries, eraseRetainedBoundary, hib]

/-- finite-set 削除に一点を追加することは、その一点削除を後から行うことと同じ。 -/
theorem eraseRetainedBoundaries_insert
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (E : Finset (InternalRecordBoundary D))
    (b : InternalRecordBoundary D) :
    eraseRetainedBoundaries R (insert b E) =
      eraseRetainedBoundary (eraseRetainedBoundaries R E) b := by
  funext i
  by_cases hib : i = b
  · subst i
    simp [eraseRetainedBoundaries, eraseRetainedBoundary]
  · simp [eraseRetainedBoundaries, eraseRetainedBoundary, hib]

/-- 複数削除の合成は削除集合の union。 -/
theorem eraseRetainedBoundaries_union
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (E F : Finset (InternalRecordBoundary D)) :
    eraseRetainedBoundaries (eraseRetainedBoundaries R E) F =
      eraseRetainedBoundaries R (E ∪ F) := by
  funext b
  by_cases hbE : b ∈ E <;> by_cases hbF : b ∈ F <;>
    simp [eraseRetainedBoundaries, hbE, hbF]

/-- finite-set 削除は Boolean 順序を下向きに進む。 -/
theorem eraseRetainedBoundaries_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (E : Finset (InternalRecordBoundary D)) :
    (eraseRetainedBoundaries R E).Le R := by
  intro b hb
  by_cases hbE : b ∈ E
  · simp [eraseRetainedBoundaries, hbE] at hb
  · simpa [eraseRetainedBoundaries, hbE] using hb

/--
`R` から `S` へ進むときに消すべき境界の exact difference set。
`S.Le R` の下では、R で true かつ S で false の境界だけが入る。
-/
def deletedBoundarySet
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    Finset (InternalRecordBoundary D) := by
  letI : DecidablePred
      (fun b : InternalRecordBoundary D =>
        R b = true ∧ S b = false) :=
    fun b => inferInstance
  exact Finset.univ.filter
    (fun b => R b = true ∧ S b = false)

@[simp] theorem mem_deletedBoundarySet
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    b ∈ deletedBoundarySet D R S ↔
      R b = true ∧ S b = false := by
  simp [deletedBoundarySet]

/-- Boolean 下向き順序では difference set を消せば target pattern を exact に復元できる。 -/
theorem eraseRetainedBoundaries_deletedBoundarySet
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    eraseRetainedBoundaries R (deletedBoundarySet D R S) = S := by
  funext b
  cases hR : R b <;> cases hS : S b
  · simp [eraseRetainedBoundaries, deletedBoundarySet, hR, hS]
  · exfalso
    have h := hSR b (by simpa using hS)
    simp [hR] at h
  · simp [eraseRetainedBoundaries, deletedBoundarySet, hR, hS]
  · simp [eraseRetainedBoundaries, deletedBoundarySet, hR, hS]

/-- Boolean 順序は finite deleted-boundary set による到達可能性と同値。 -/
theorem retainedLe_iff_exists_eraseRetainedBoundaries
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    S.Le R ↔
      ∃ E : Finset (InternalRecordBoundary D),
        S = eraseRetainedBoundaries R E := by
  constructor
  · intro hSR
    refine ⟨deletedBoundarySet D R S, ?_⟩
    exact (eraseRetainedBoundaries_deletedBoundarySet hSR).symm
  · rintro ⟨E, rfl⟩
    exact eraseRetainedBoundaries_le R E

/-- R で保持されている全境界を消すと全消去 pattern になる。 -/
theorem eraseRetainedBoundaries_retainedBoundarySet
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) :
    eraseRetainedBoundaries R (retainedBoundarySet D R) =
      retainNoBoundaries D := by
  funext b
  cases hR : R b with
  | false =>
      have hbNot : b ∉ retainedBoundarySet D R := by
        simp [retainedBoundarySet, hR]
      simp [eraseRetainedBoundaries, retainNoBoundaries, hbNot, hR]
  | true =>
      have hbMem : b ∈ retainedBoundarySet D R := by
        simp [retainedBoundarySet, hR]
      simp [eraseRetainedBoundaries, retainNoBoundaries, hbMem]

/-! ## 3. actual 一段削除の反射推移閉包 -/

/--
P34 actual 一段削除の有限 reachability。
`refl` は 0 回、`tail` は既存経路の末尾に一段を追加する。
-/
inductive ActualCanonicalDeletionReachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    RetainedBoundaryPattern D → RetainedBoundaryPattern D → Prop
  | refl (R : RetainedBoundaryPattern D) :
      ActualCanonicalDeletionReachable P hPrimitive hReduced u D R R
  | tail {R S T : RetainedBoundaryPattern D} :
      ActualCanonicalDeletionReachable P hPrimitive hReduced u D R S →
      ActualCanonicalBoundaryDeletion P hPrimitive hReduced u D S T →
      ActualCanonicalDeletionReachable P hPrimitive hReduced u D R T

namespace ActualCanonicalDeletionReachable

/-- reachability は推移的。 -/
theorem trans
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S T : RetainedBoundaryPattern D}
    (hRS : ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R S)
    (hST : ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D S T) :
    ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R T := by
  induction hST with
  | refl =>
      exact hRS
  | tail hAB hBC ih =>
      exact ActualCanonicalDeletionReachable.tail ih hBC

/-- actual reachability は pattern inclusion を下向きにしか進まない。 -/
theorem pattern_le
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hRS : ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R S) :
    S.Le R := by
  induction hRS with
  | refl =>
      exact RetainedBoundaryPattern.le_refl R
  | tail hAB A ih =>
      exact RetainedBoundaryPattern.le_trans A.pattern_step.le ih

end ActualCanonicalDeletionReachable

/-- active な finite set の境界は actual 一段削除を反復して全部消せる。 -/
theorem actualReachable_eraseRetainedBoundaries
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (E : Finset (InternalRecordBoundary D))
    (hActive : ∀ b ∈ E, R b = true) :
    ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R
      (eraseRetainedBoundaries R E) := by
  classical
  revert hActive
  refine Finset.induction_on E ?_ ?_
  · intro _
    simpa using
      (ActualCanonicalDeletionReachable.refl
        (P := P) (hPrimitive := hPrimitive) (hReduced := hReduced)
        (u := u) (D := D) R)
  · intro b E hb ih hActive
    have hActiveE : ∀ i ∈ E, R i = true := by
      intro i hi
      exact hActive i (by simp [hi])
    have hRb : R b = true := hActive b (by simp)
    have hReachE := ih hActiveE
    have hbCurrent : eraseRetainedBoundaries R E b = true := by
      simp [eraseRetainedBoundaries, hb, hRb]
    have hStep :
        ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D
          (eraseRetainedBoundaries R E)
          (eraseRetainedBoundary (eraseRetainedBoundaries R E) b) :=
      actualCanonicalBoundaryDeletion_of_pattern
        P hPrimitive hReduced u D
        ⟨b, hbCurrent, rfl⟩
    have hTail :=
      ActualCanonicalDeletionReachable.tail hReachE hStep
    rw [eraseRetainedBoundaries_insert]
    exact hTail

/-- Boolean 順序 `S.Le R` なら actual 一段削除列で R から S へ到達できる。 -/
theorem actualReachable_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R S := by
  let E := deletedBoundarySet D R S
  have hActive : ∀ b ∈ E, R b = true := by
    intro b hb
    have h := (mem_deletedBoundarySet R S b).1 hb
    exact h.1
  have hReach :=
    actualReachable_eraseRetainedBoundaries
      P hPrimitive hReduced u D R E hActive
  have hTarget : eraseRetainedBoundaries R E = S := by
    dsimp [E]
    exact eraseRetainedBoundaries_deletedBoundarySet hSR
  rw [hTarget] at hReach
  exact hReach

/--
## 到達可能性主定理

actual canonical deletion の有限反復は、Boolean 境界順序と exact に同値。
-/
theorem actualReachable_iff_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D R S ↔
      S.Le R := by
  constructor
  · intro hReach
    exact ActualCanonicalDeletionReachable.pattern_le
      P hPrimitive hReduced u D hReach
  · intro hLe
    exact actualReachable_of_retainedLe
      P hPrimitive hReduced u D hLe

/-! ## 4. 停止性と normal form -/

/--
一段 actual deletion を逆向き引数順で見ると well-founded。
測度は `retainedBoundaryCount` で、一段ごとに exact に 1 減る。
-/
theorem actualCanonicalBoundaryDeletion_wellFounded
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    WellFounded
      (fun S R : RetainedBoundaryPattern D =>
        ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D R S) := by
  refine (measure (retainedBoundaryCount D)).wf.mono ?_
  intro S R hStep
  exact ActualCanonicalBoundaryDeletion.count_lt
    P hPrimitive hReduced u D hStep

/-- outgoing actual deletion を一つも持たない pattern。 -/
def ActualCanonicalDeletionNormal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : Prop :=
  ∀ S : RetainedBoundaryPattern D,
    ¬ ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S

/-- actual normal pattern は全消去 pattern に限り、逆も成り立つ。 -/
theorem actualCanonicalDeletionNormal_iff_eq_none
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ActualCanonicalDeletionNormal
        P hPrimitive hReduced u D R ↔
      R = retainNoBoundaries D := by
  constructor
  · intro hNormal
    funext b
    cases hRb : R b with
    | false =>
        simp [retainNoBoundaries]
    | true =>
        have hStep :
            ActualCanonicalBoundaryDeletion
              P hPrimitive hReduced u D R
              (eraseRetainedBoundary R b) :=
          actualCanonicalBoundaryDeletion_of_pattern
            P hPrimitive hReduced u D
            ⟨b, hRb, rfl⟩
        exact (hNormal _ hStep).elim
  · intro hEq S hStep
    rw [hEq] at hStep
    rcases hStep.pattern_step with ⟨b, hb, _⟩
    simp [retainNoBoundaries] at hb

/-- normal pattern は一意。 -/
theorem actualCanonicalDeletionNormal_unique
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hR : ActualCanonicalDeletionNormal
      P hPrimitive hReduced u D R)
    (hS : ActualCanonicalDeletionNormal
      P hPrimitive hReduced u D S) :
    R = S := by
  have hR0 :=
    (actualCanonicalDeletionNormal_iff_eq_none
      P hPrimitive hReduced u D R).1 hR
  have hS0 :=
    (actualCanonicalDeletionNormal_iff_eq_none
      P hPrimitive hReduced u D S).1 hS
  exact hR0.trans hS0.symm

/-- 任意の pattern は一意な全消去 normal pattern へ actual に到達する。 -/
theorem actualReachable_to_none
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R (retainNoBoundaries D) :=
  actualReachable_of_retainedLe
    P hPrimitive hReduced u D
    (RetainedBoundaryPattern.none_le D R)

/-- 標準平坦 family で全消去 FiberPoint と一致するのは全消去 pattern だけ。 -/
theorem canonicalFlatPoint_eq_canonicalNoBoundaryPoint_iff
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    canonicalFlatPoint P hPrimitive hReduced u D R =
        canonicalNoBoundaryPoint P hPrimitive hReduced u D ↔
      R = retainNoBoundaries D := by
  constructor
  · intro hPoint
    apply canonicalFlatPoint_injective P hPrimitive hReduced u D
    simpa [canonicalNoBoundaryPoint] using hPoint
  · intro hR
    subst R
    rfl

/-! ## 5. 削除順序非依存と合流 -/

/-- finite deletion sets の二段合成 endpoint は union だけで決まり、順序に依存しない。 -/
theorem finiteDeletion_union_endpoint
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (E F : Finset (InternalRecordBoundary D)) :
    canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundaries (eraseRetainedBoundaries R E) F) =
      canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundaries (eraseRetainedBoundaries R F) E) := by
  rw [eraseRetainedBoundaries_union, eraseRetainedBoundaries_union]
  apply congrArg (canonicalFlatPoint P hPrimitive hReduced u D)
  exact congrArg (eraseRetainedBoundaries R) (Finset.union_comm E F)

/--
任意の二つの保持 pattern `S`, `T` は、
actual deletion を有限回行うことで同じ pattern `U` へ到達できる。
したがって actual deletion の到達関係は global に joinable である。
-/
theorem actualCanonicalDeletionReachable_joinable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {S T : RetainedBoundaryPattern D} :
    ∃ U : RetainedBoundaryPattern D,
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D S U ∧
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D T U := by
  refine ⟨retainNoBoundaries D, ?_, ?_⟩
  · exact actualReachable_to_none P hPrimitive hReduced u D S
  · exact actualReachable_to_none P hPrimitive hReduced u D T

/--
一段 actual fork も local diamond を持つ。同じ境界を消した場合は target が同一、
異なる境界なら両方を消した common successor が actual に存在する。
-/
theorem actualCanonicalBoundaryDeletion_localConfluence
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S T : RetainedBoundaryPattern D}
    (A : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S)
    (B : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R T) :
    S = T ∨
      ∃ U : RetainedBoundaryPattern D,
        ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D S U ∧
        ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D T U := by
  rcases A.pattern_step with ⟨a, ha, hS⟩
  rcases B.pattern_step with ⟨b, hb, hT⟩
  by_cases hab : a = b
  · left
    subst b
    exact hS.trans hT.symm
  · right
    let U := eraseRetainedBoundary (eraseRetainedBoundary R a) b
    have hba : b ≠ a := by
      intro hba
      exact hab hba.symm
    have hbAfter : eraseRetainedBoundary R a b = true := by
      simp [eraseRetainedBoundary, hba, hb]
    have haAfter : eraseRetainedBoundary R b a = true := by
      simp [eraseRetainedBoundary, hab, ha]
    have hSU : CanonicalBoundaryDeletion D S U := by
      rw [hS]
      exact ⟨b, hbAfter, rfl⟩
    have hTU : CanonicalBoundaryDeletion D T U := by
      rw [hT]
      refine ⟨a, haAfter, ?_⟩
      dsimp [U]
      exact eraseRetainedBoundary_comm R a b
    exact ⟨U,
      actualCanonicalBoundaryDeletion_of_pattern
        P hPrimitive hReduced u D hSU,
      actualCanonicalBoundaryDeletion_of_pattern
        P hPrimitive hReduced u D hTU⟩

/-! ## 6. 最終 closure theorem -/

/--
P29--P35 の canonical Boolean / Ferrers deformation family が満たす閉包データ。

`termination` は actual 一段 relation の well-foundedness、`reachability_exact` は
その有限反復と Boolean inclusion の exact equivalence、`normal_form_exact` は全消去の一意性、
`confluence` は任意の二経路の共通 descendant を記録する。
-/
structure CanonicalActualDeletionSystemClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  family_card :
    Fintype.card (RetainedBoundaryPattern D) =
      2 ^ (D.lengths.length - 1)
  termination :
    WellFounded
      (fun S R : RetainedBoundaryPattern D =>
        ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D R S)
  reachability_exact :
    ∀ R S : RetainedBoundaryPattern D,
      ActualCanonicalDeletionReachable
          P hPrimitive hReduced u D R S ↔
        S.Le R
  normal_form_exact :
    ∀ R : RetainedBoundaryPattern D,
      ActualCanonicalDeletionNormal
          P hPrimitive hReduced u D R ↔
        R = retainNoBoundaries D
  every_pattern_normalizes :
    ∀ R : RetainedBoundaryPattern D,
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D R (retainNoBoundaries D)
  endpoint_firstCrossing :
    FirstCrossing
      (canonicalNoBoundaryPoint
        P hPrimitive hReduced u D).word
  endpoint_exact :
    ∀ R : RetainedBoundaryPattern D,
      canonicalFlatPoint P hPrimitive hReduced u D R =
          canonicalNoBoundaryPoint P hPrimitive hReduced u D ↔
        R = retainNoBoundaries D
  local_confluence :
    ∀ {R S T : RetainedBoundaryPattern D},
      ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D R S →
      ActualCanonicalBoundaryDeletion
          P hPrimitive hReduced u D R T →
      S = T ∨
        ∃ U : RetainedBoundaryPattern D,
          ActualCanonicalBoundaryDeletion
              P hPrimitive hReduced u D S U ∧
          ActualCanonicalBoundaryDeletion
              P hPrimitive hReduced u D T U
  confluence :
    ∀ {R S T : RetainedBoundaryPattern D},
      ActualCanonicalDeletionReachable
          P hPrimitive hReduced u D R S →
      ActualCanonicalDeletionReachable
          P hPrimitive hReduced u D R T →
      ∃ U : RetainedBoundaryPattern D,
        ActualCanonicalDeletionReachable
            P hPrimitive hReduced u D S U ∧
        ActualCanonicalDeletionReachable
            P hPrimitive hReduced u D T U

/--
## Record--Ferrers canonical deletion closure theorem

標準平坦 Boolean family 上の actual boundary deletion 系は有限で停止し、
Boolean inclusion と exact に一致する到達可能性を持ち、全消去 pattern / `canonicalNoBoundaryPoint`
を一意な normal form として持つ合流的 deformation system である。
-/
theorem canonicalActualDeletionSystem_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    CanonicalActualDeletionSystemClosed
      P hPrimitive hReduced u D := by
  refine {
    family_card := retainedBoundaryPattern_card D
    termination := actualCanonicalBoundaryDeletion_wellFounded
      P hPrimitive hReduced u D
    reachability_exact := ?_
    normal_form_exact := ?_
    every_pattern_normalizes := ?_
    endpoint_firstCrossing :=
      canonicalNoBoundaryPoint_firstCrossing
        P hPrimitive hReduced u D
    endpoint_exact := ?_
    local_confluence := ?_
    confluence := ?_
  }
  · intro R S
    exact actualReachable_iff_retainedLe
      P hPrimitive hReduced u D R S
  · intro R
    exact actualCanonicalDeletionNormal_iff_eq_none
      P hPrimitive hReduced u D R
  · intro R
    exact actualReachable_to_none
      P hPrimitive hReduced u D R
  · intro R
    exact canonicalFlatPoint_eq_canonicalNoBoundaryPoint_iff
      P hPrimitive hReduced u D R
  · intro R S T hRS hRT
    exact actualCanonicalBoundaryDeletion_localConfluence
      P hPrimitive hReduced u D hRS hRT
  · intro R S T hRS hRT
    exact actualCanonicalDeletionReachable_joinable
      P hPrimitive hReduced u D

end RecordFerrers
end Collatz2
