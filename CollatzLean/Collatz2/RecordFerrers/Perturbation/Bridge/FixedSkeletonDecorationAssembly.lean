import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ProperLocalDecorationSupport
import CollatzLean.Collatz2.RecordFerrers.Factorization.PrimitiveReducedInverse
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.TranslationCoordinates

/-!
# Record–Ferrers Perturbation / Fixed Skeleton Decoration Assembly

`ProperLocalDecorationSupport` までで、actual→flat-top interval の one-cell rewrite は
元 source と同じ canonical record skeleton を保ち、さらに各 edge は一つの genuine
record block の内部に support を持つことが分かった。

本ファイルでは逆方向を閉じる。

固定した genuine decomposition

  D.lengths = [r₁, r₂, ..., rₘ]

に対して、各 length `rᵢ` の genuine `LocalDecoration rᵢ` を互いに独立に選び、
その任意の tuple を同じ fixed chord 上の genuine FirstCrossing / RecordDecomposition
へ assembly できることを示す。

重要なのは carry gluing が local word の arithmetic translation を見ず、length list
だけを見ることである。従って `D.lengths` が既に満たす full carry condition は、
各 block decoration を任意に差し替えた後もそのまま使える。

最終的に再構成された decomposition の block list が、選択した local decoration の
word listそのものに exact に一致するところまで閉じる。従ってこれは単なる existence
ではなく、固定 skeleton 上の local decorations の真正な独立 assembly である。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. length list 上の dependent local-decoration tuple -/

/--
length list `[r₁,...,rₘ]` の各成分に一つずつ `LocalDecoration rᵢ` を載せた dependent tuple。
各成分は他成分の word / affine translation を一切参照しない。
-/
inductive LocalDecorationTuple : List ℕ → Type
  | nil : LocalDecorationTuple []
  | cons {r : ℕ} {rs : List ℕ} :
      LocalDecoration r →
      LocalDecorationTuple rs →
      LocalDecorationTuple (r :: rs)

namespace LocalDecorationTuple

/-- tuple から concrete local block word list を忘却する。 -/
def blocks {rs : List ℕ} (T : LocalDecorationTuple rs) : List Word :=
  match T with
  | .nil => []
  | .cons A T => A.word :: blocks T

@[simp] theorem blocks_nil :
    blocks LocalDecorationTuple.nil = [] := rfl

@[simp] theorem blocks_cons
    {r : ℕ}
    {rs : List ℕ}
    (A : LocalDecoration r)
    (T : LocalDecorationTuple rs) :
    blocks (LocalDecorationTuple.cons A T) = A.word :: blocks T := rfl

/-- block word list の odd lengths は index length list に exact に戻る。 -/
@[simp] theorem blocks_oddSteps
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    T.blocks.map oddSteps = rs := by
  induction T with
  | nil => rfl
  | @cons r rs A T ih =>
      simp [blocks, A.length_eq, ih]

/-- tuple の全 block words は MinimalBlock。 -/
theorem blocks_minimal
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    ∀ b ∈ T.blocks, MinimalBlock b := by
  induction T with
  | nil =>
      intro b hb
      simp [blocks] at hb
  | @cons r rs A T ih =>
      intro b hb
      simp only [blocks_cons, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact A.validMinimal.toMinimalBlock
      · exact ih b hb

/-- tuple の全 block words は Valid。 -/
theorem blocks_valid
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    ∀ b ∈ T.blocks, Valid b := by
  induction T with
  | nil =>
      intro b hb
      simp [blocks] at hb
  | @cons r rs A T ih =>
      intro b hb
      simp only [blocks_cons, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact A.validMinimal.valid
      · exact ih b hb

/-- tuple の全 block words は genuine valid minimal blocks。 -/
theorem blocks_validMinimal
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    ∀ b ∈ T.blocks, ValidMinimalBlock b := by
  intro b hb
  exact {
    toMinimalBlock := T.blocks_minimal b hb
    valid := T.blocks_valid b hb
  }

/-- dependent tuple は同じ length list の `ValidDecoratedSkeleton` を直接与える。 -/
def toValidDecoratedSkeleton
    {S : Skeleton}
    (T : LocalDecorationTuple S.lengths) :
    ValidDecoratedSkeleton S :=
  { toDecoratedSkeleton := {
      blocks := T.blocks
      lengths_eq := T.blocks_oddSteps
      minimal := T.blocks_minimal
    }
    valid := T.blocks_valid
  }

@[simp] theorem toValidDecoratedSkeleton_blocks
    {S : Skeleton}
    (T : LocalDecorationTuple S.lengths) :
    T.toValidDecoratedSkeleton.blocks = T.blocks := rfl

end LocalDecorationTuple

/-! ## 2. factorization から chosen block list を exact に切り戻す -/

/--
`x.word = anchor ++ bs.flatten` なら、`bs.map oddSteps` を使った canonical slicing は
元の `bs` を exact に返す。

これは inverse construction 後の `RecordDecomposition.blocks` が、assembly に与えた
local decorations そのものになることを保証する pure list-slicing lemma。
-/
theorem blockWordsFromLengths_eq_of_factorization
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor : Word)
    (bs : List Word)
    (hWord : x.word = anchor ++ bs.flatten) :
    RecordChain.blockWordsFromLengths
        x (oddSteps anchor) (bs.map oddSteps) = bs := by
  induction bs generalizing anchor with
  | nil =>
      simp [RecordChain.blockWordsFromLengths]
  | cons b bs ih =>
      have hHead :
          blockWord x (oddSteps anchor) (oddSteps b) = b :=
        blockWord_eq_head_of_factorization
          x anchor b bs hWord
      have hTailWord :
          x.word = (anchor ++ b) ++ bs.flatten := by
        simpa [List.append_assoc] using hWord
      have hTail := ih (anchor := anchor ++ b) hTailWord
      have hTail' :
          RecordChain.blockWordsFromLengths
              x (oddSteps anchor + oddSteps b) (bs.map oddSteps) = bs := by
        simpa [oddSteps_append] using hTail
      simp only [List.map_cons, RecordChain.blockWordsFromLengths]
      rw [hHead, hTail']

/-! ## 3. fixed start-1 anchor -/

/-- fixed-skeleton assembly で保持する initial anchor prefix。 -/
def fixedSkeletonAnchor
    {p H : ℕ}
    (u : FiberPoint p H) : Word :=
  u.word.take 1

/-- genuine decomposition の chain start は critical roof 上にある。 -/
theorem RecordDecomposition.start_roof_public
    {p H : ℕ}
    {u : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition u start) :
    u.height start = criticalHeight start :=
  D.startHeight_eq_criticalHeight

/-- cut 1 decomposition の initial anchor は exact に one odd step。 -/
theorem fixedSkeletonAnchor_oddSteps
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1) :
    oddSteps (fixedSkeletonAnchor u) = 1 := by
  have hp : 1 < p := by
    rcases D with ⟨lengths, chain⟩
    cases chain with
    | last B hTerminal =>
        have hLenPos := B.length_pos
        omega
    | cons B hInterior T =>
        have hLenPos := B.length_pos
        omega
  have hLen : u.word.length = p := by
    simpa [oddSteps] using u.oddSteps_eq
  unfold fixedSkeletonAnchor oddSteps
  rw [List.length_take, hLen]
  rw [Nat.min_eq_left (Nat.le_of_lt hp)]

/-- cut 1 anchor の total depth は critical roof height。 -/
theorem fixedSkeletonAnchor_twoSteps
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1) :
    twoSteps (fixedSkeletonAnchor u) = criticalHeight 1 := by
  have hRoof := D.start_roof_public
  change prefixTwoDepth u.word 1 = criticalHeight 1 at hRoof
  simpa [fixedSkeletonAnchor, prefixTwoDepth] using hRoof

/-- cut 1 anchor は `CriticalRoofPrefix`。 -/
theorem fixedSkeletonAnchor_criticalRoofPrefix
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1) :
    CriticalRoofPrefix (fixedSkeletonAnchor u) := by
  let a := fixedSkeletonAnchor u
  have hOdd : oddSteps a = 1 := by
    dsimp [a]
    exact fixedSkeletonAnchor_oddSteps u D
  have hRoofOne : twoSteps a = criticalHeight 1 := by
    dsimp [a]
    exact fixedSkeletonAnchor_twoSteps u D
  refine {
    roof := ?_
    prefix_le := ?_
  }
  · rw [hOdd]
    exact hRoofOne
  · intro k hkPos hkLe
    rw [hOdd] at hkLe
    have hkEq : k = 1 := by omega
    subst k
    have hTerminal :
        prefixTwoDepth a (oddSteps a) = twoSteps a := by
      simp [prefixTwoDepth, oddSteps]
    rw [hOdd] at hTerminal
    rw [hTerminal, hRoofOne]

/-! ## 4. arbitrary tuple の choice-free whole word / FiberPoint assembly -/

/-- initial anchor の後ろへ chosen local decorations をそのまま concatenate する。 -/
def assembleFixedSkeletonWord
    {p H : ℕ}
    (u : FiberPoint p H)
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) : Word :=
  fixedSkeletonAnchor u ++ T.blocks.flatten

/-- chosen tuple の block lengths は元 decomposition の skeleton と同じなので full carry を保つ。 -/
theorem localDecorationTuple_fullCarry
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    Skeleton.carryConditionFrom
      (oddSteps (fixedSkeletonAnchor u))
      (T.blocks.map oddSteps) := by
  rw [fixedSkeletonAnchor_oddSteps u D, T.blocks_oddSteps]
  exact Skeleton.carryCondition_of_decomposition D

/-- arbitrary chosen local decorations の assembled whole word は MinimalBlock。 -/
theorem assembleFixedSkeletonWord_minimalBlock
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    MinimalBlock (assembleFixedSkeletonWord u T) := by
  unfold assembleFixedSkeletonWord
  exact minimalBlock_of_blocks_carryCondition
    (fixedSkeletonAnchor u)
    T.blocks
    (fixedSkeletonAnchor_criticalRoofPrefix u D)
    T.blocks_minimal
    (localDecorationTuple_fullCarry u D T)

/-- arbitrary chosen local decorations の assembled whole word は FirstCrossing。 -/
theorem assembleFixedSkeletonWord_firstCrossing
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    FirstCrossing (assembleFixedSkeletonWord u T) :=
  (assembleFixedSkeletonWord_minimalBlock u D T).firstCrossing

/-- assembled whole word は genuine positive exponent word。 -/
theorem assembleFixedSkeletonWord_valid
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    Valid (assembleFixedSkeletonWord u T) := by
  unfold assembleFixedSkeletonWord fixedSkeletonAnchor
  have hAnchor : Valid (u.word.take 1) :=
    FiberPoint.valid_take u.valid 1
  have hBlocks : Valid T.blocks.flatten :=
    valid_flatten_of_all_public T.blocks T.blocks_valid
  exact hAnchor.append hBlocks

/-- assembled whole word の odd length は元 fixed fiber の `p`。 -/
theorem assembleFixedSkeletonWord_oddSteps
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    oddSteps (assembleFixedSkeletonWord u T) = p := by
  unfold assembleFixedSkeletonWord
  rw [oddSteps_append, oddSteps_flatten_blocks]
  rw [fixedSkeletonAnchor_oddSteps u D]
  unfold blockOddSteps
  rw [T.blocks_oddSteps]
  exact D.start_add_sum_eq_terminal

/-- assembled whole word の total two-depth も元 fixed fiber の `H`。 -/
theorem assembleFixedSkeletonWord_twoSteps
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    twoSteps (assembleFixedSkeletonWord u T) = H := by
  have hDepth :=
    (assembleFixedSkeletonWord_minimalBlock u D T).minimalDepth
  rw [assembleFixedSkeletonWord_oddSteps u D T] at hDepth
  exact hDepth.trans
    D.twoDepth_eq_criticalHeight_add_one.symm

/-- arbitrary tuple を元 `(p,H)` fixed fiber の genuine point へ choice-free に assembly。 -/
def assembleFixedSkeletonPoint
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    FiberPoint p H :=
  { word := assembleFixedSkeletonWord u T
    valid := assembleFixedSkeletonWord_valid u D T
    oddSteps_eq := assembleFixedSkeletonWord_oddSteps u D T
    twoSteps_eq := assembleFixedSkeletonWord_twoSteps u D T
  }

@[simp] theorem assembleFixedSkeletonPoint_word
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    (assembleFixedSkeletonPoint u D T).word =
      assembleFixedSkeletonWord u T := rfl

/-- assembled point も FirstCrossing。 -/
theorem assembleFixedSkeletonPoint_firstCrossing
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    FirstCrossing (assembleFixedSkeletonPoint u D T).word := by
  exact assembleFixedSkeletonWord_firstCrossing u D T

/-! ## 5. primitive/reduced inverse による genuine RecordDecomposition recovery -/

namespace RecordDecomposition

/-- start index の equality に沿って decomposition を transport する。 -/
def castStart
    {p H : ℕ}
    {x : FiberPoint p H}
    {start stop : ℕ}
    (D : RecordDecomposition x start)
    (h : start = stop) :
    RecordDecomposition x stop := by
  subst stop
  exact D

@[simp] theorem castStart_lengths
    {p H : ℕ}
    {x : FiberPoint p H}
    {start stop : ℕ}
    (D : RecordDecomposition x start)
    (h : start = stop) :
    (D.castStart h).lengths = D.lengths := by
  subst stop
  rfl

@[simp] theorem castStart_blocks
    {p H : ℕ}
    {x : FiberPoint p H}
    {start stop : ℕ}
    (D : RecordDecomposition x start)
    (h : start = stop) :
    (D.castStart h).blocks = D.blocks := by
  subst stop
  rfl

end RecordDecomposition

/--
fixed skeleton 上の arbitrary local-decoration tuple の explicit assembly result。
`blocks_eq` により、inverse 後の genuine record blocks は chosen tuple と exact に一致する。
-/
structure FixedSkeletonAssemblyResult
    {p H : ℕ}
    (u : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) where
  point : FiberPoint p H
  decomposition : RecordDecomposition point 1
  lengths_eq : decomposition.lengths = D.lengths
  blocks_eq : decomposition.blocks = T.blocks

/--
## Fixed Skeleton Decoration Assembly 主構成

primitive + StripReduced fixed chord 上では、元 skeleton `D.lengths` の各成分に置いた
任意 local decoration tuple を genuine FirstCrossing point / RecordDecomposition へ assembly
でき、回収された block list は chosen tuple と exact に一致する。
-/
def assembleFixedSkeleton
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    FixedSkeletonAssemblyResult u D T := by
  let x : FiberPoint P.oddCount P.twoDepth :=
    assembleFixedSkeletonPoint u D T
  let anchor : Word := fixedSkeletonAnchor u
  let bs : List Word := T.blocks
  have hWord : x.word = anchor ++ bs.flatten := by
    rfl
  have hNonempty : bs ≠ [] := by
    intro hNil
    apply D.lengths_nonempty
    calc
      D.lengths = bs.map oddSteps := T.blocks_oddSteps.symm
      _ = [] := by simp [hNil]
  have hAnchorOdd : oddSteps anchor = 1 := by
    dsimp [anchor]
    exact fixedSkeletonAnchor_oddSteps u D
  have hAnchorPos : 0 < oddSteps anchor := by
    rw [hAnchorOdd]
    omega
  have hMinimal : ∀ b ∈ bs, MinimalBlock b := by
    dsimp [bs]
    exact T.blocks_minimal
  have hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor) := by
    exact (fixedSkeletonAnchor_criticalRoofPrefix u D).roof
  have hCarry :
      Skeleton.carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps) := by
    dsimp [anchor, bs]
    exact localDecorationTuple_fullCarry u D T
  have hWhole : FirstCrossing x.word := by
    dsimp [x]
    exact assembleFixedSkeletonPoint_firstCrossing u D T
  have hPrimitiveX :
      (x.toContractingExponentPair hWhole).IsPrimitive := by
    simpa [FiberPoint.toContractingExponentPair] using hPrimitive
  have hReducedX :
      (x.toContractingExponentPair hWhole).StripReduced := by
    simpa [FiberPoint.toContractingExponentPair] using hReduced
  let E0 : RecordDecomposition x (oddSteps anchor) :=
    recordDecomposition_of_primitiveReduced_fullCarry
      x anchor bs hWord hNonempty hAnchorPos hMinimal hAnchorRoof
      hCarry hWhole hPrimitiveX hReducedX
  have hE0Lengths : E0.lengths = D.lengths := by
    change bs.map oddSteps = D.lengths
    dsimp [bs]
    exact T.blocks_oddSteps
  have hE0Blocks : E0.blocks = bs := by
    change
      RecordChain.blockWordsFromLengths
          x (oddSteps anchor) (bs.map oddSteps) = bs
    exact blockWordsFromLengths_eq_of_factorization
      x anchor bs hWord
  let E : RecordDecomposition x 1 :=
    E0.castStart hAnchorOdd
  refine {
    point := x
    decomposition := E
    lengths_eq := ?_
    blocks_eq := ?_
  }
  · dsimp [E]
    rw [RecordDecomposition.castStart_lengths]
    exact hE0Lengths
  · dsimp [E]
    rw [RecordDecomposition.castStart_blocks]
    exact hE0Blocks

namespace FixedSkeletonAssemblyResult

/-- assembly result の whole point は FirstCrossing。 -/
theorem firstCrossing
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {T : LocalDecorationTuple D.lengths}
    (A : FixedSkeletonAssemblyResult u D T) :
    FirstCrossing A.point.word :=
  A.decomposition.whole_firstCrossing

end FixedSkeletonAssemblyResult

/--
## 主定理: fixed skeleton 上の local decorations は任意に独立選択可能

各 coordinate `rᵢ` では `LocalDecoration rᵢ` を自由に選べる。
選択後に必要な global compatibility は元 `D.lengths` の carry condition だけであり、
各 local decoration の arithmetic translation 同士を結ぶ追加 gluing condition は存在しない。

しかも resulting decomposition の block list は chosen tuple と exact に一致する。
-/
theorem exists_actual_realization_of_arbitrary_localDecorations
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    ∃ x : FiberPoint P.oddCount P.twoDepth,
      ∃ E : RecordDecomposition x 1,
        E.lengths = D.lengths ∧
        E.blocks = T.blocks := by
  let A := assembleFixedSkeleton P hPrimitive hReduced u D T
  exact ⟨A.point, A.decomposition, A.lengths_eq, A.blocks_eq⟩

/-- fixed skeleton independent-assembly closure package。 -/
structure FixedSkeletonDecorationAssemblyClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  arbitrary_local_tuple_realizable :
    ∀ T : LocalDecorationTuple D.lengths,
      ∃ x : FiberPoint P.oddCount P.twoDepth,
        ∃ E : RecordDecomposition x 1,
          E.lengths = D.lengths ∧
          E.blocks = T.blocks

/--
## Fixed Skeleton Decoration Assembly closure theorem

固定 genuine record skeleton の各 local decoration coordinate は mutually independent:
各 `LocalDecoration rᵢ` を任意に選んだ tuple は、同じ primitive/reduced fixed chord 上の
genuine actual RecordDecomposition として exact に実現される。
-/
theorem fixedSkeletonDecorationAssembly_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonDecorationAssemblyClosed
      P hPrimitive hReduced u D := by
  refine {
    arbitrary_local_tuple_realizable := ?_
  }
  intro T
  exact exists_actual_realization_of_arbitrary_localDecorations
    P hPrimitive hReduced u D T

end RecordFerrers
end Collatz2
