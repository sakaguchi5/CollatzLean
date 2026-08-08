import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentAffineBounds
import CollatzLean.CollatzSecondLayer3.ActualReturn.ExactAdjacency
import CollatzLean.CollatzSecondLayer3.ActualReturn.LateNextMinimum
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# Adjacent Contracting Return から旧 first-crossing 資産への bridge

whole adjacent word が contracting なら、同じ future-minimum から有限 first crossing が
必ず存在する。その最小長 `p` は adjacent gap `r` 以下であり、

* `p = r` : ExactAdjacency
* `p < r` : LateNextMinimum

へ戻る。

さらに contracting adjacent tower 上では selected future-minimum 値が発散するため、
この最小 first-crossing 長も無限大へ進む。従って旧 Exact/Late tower の
`lengths_tend_to_infinity` も新仮定なしで復元できる。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace AdjacentContractingReturnData

/--
whole contracting adjacent segment 自身は expanding ではない。
-/
theorem whole_not_expanding
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    ¬ Expanding
      (O.segmentWord D.state.startIndex D.state.length) := by
  intro hExp
  have hCon : Contracting D.state.word := by
    simpa [
      AdjacentContractingReturnAt,
      AdjacentFutureMinimumReturnData.word
    ] using D.contracting
  change
    Contracting
      (O.segmentWord D.state.startIndex D.state.length)
    at hCon
  change
    2 ^ (O.segmentWord D.state.startIndex D.state.length).twoSteps <
      3 ^ (O.segmentWord D.state.startIndex D.state.length).oddSteps
    at hExp
  change
    3 ^ (O.segmentWord D.state.startIndex D.state.length).oddSteps <
      2 ^ (O.segmentWord D.state.startIndex D.state.length).twoSteps
    at hCon
  omega


/--
whole contracting adjacent segment 自身が非 expanding segment の証人。
-/
theorem has_nonexpanding_segment
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    ∃ p : ℕ,
      0 < p ∧
        ¬ Expanding
          (O.segmentWord D.state.startIndex p) := by
  exact
    ⟨D.state.length,
      D.state.length_pos,
      D.whole_not_expanding⟩


/--
contracting adjacent segment 内の最小 first-crossing 長。
-/
noncomputable def firstCrossingLength
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) : ℕ := by
  classical
  exact Nat.find D.has_nonexpanding_segment


/--
最小 first-crossing 長は正で、その長さでは非 expanding。
-/
theorem firstCrossingLength_spec
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    0 < D.firstCrossingLength ∧
      ¬ Expanding
        (O.segmentWord
          D.state.startIndex
          D.firstCrossingLength) := by
  classical
  unfold firstCrossingLength
  exact Nat.find_spec D.has_nonexpanding_segment


/--
最小性。
-/
theorem firstCrossingLength_min
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O)
    {q : ℕ}
    (hqPos : 0 < q)
    (hq :
      ¬ Expanding
        (O.segmentWord D.state.startIndex q)) :
    D.firstCrossingLength ≤ q := by
  classical
  unfold firstCrossingLength
  exact
    Nat.find_min'
      D.has_nonexpanding_segment
      ⟨hqPos, hq⟩


/--
最小 first-crossing は adjacent gap 以下。
-/
theorem firstCrossingLength_le_length
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    D.firstCrossingLength ≤ D.state.length := by
  exact
    D.firstCrossingLength_min
      D.state.length_pos
      D.whole_not_expanding


/--
最小非 expanding prefix は actual first crossing。
-/
theorem firstCrossing
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    FirstCrossingAt
      O
      D.state.startIndex
      D.firstCrossingLength := by
  let p := D.firstCrossingLength
  have hp :
      0 < p ∧
        ¬ Expanding
          (O.segmentWord D.state.startIndex p) := by
    simpa [p] using D.firstCrossingLength_spec
  have hne :
      O.segmentWord D.state.startIndex p ≠ [] :=
    segmentWord_nonempty_of_length_pos hp.1
  have hminimal :
      ∀ q : ℕ,
        0 < q →
        ¬ Expanding
          (O.segmentWord D.state.startIndex q) →
        p ≤ q := by
    intro q hqPos hq
    simpa [p] using
      D.firstCrossingLength_min hqPos hq
  have hproper :
      ProperPrefixesExpanding
        (O.segmentWord D.state.startIndex p) :=
    properPrefixesExpanding_of_minimal_nonexpanding
      O D.state.startIndex p hminimal
  have hvalid :
      Valid
        (O.segmentWord D.state.startIndex p) :=
    (O.runs_segment D.state.startIndex p).valid
  have hcontract :
      Contracting
        (O.segmentWord D.state.startIndex p) :=
    contracting_of_valid_nonempty_not_expanding
      hvalid hne hp.2
  exact ⟨hne, hproper, hcontract⟩


/--
旧 StandardFutureMinimumReturnData へ局所的に戻す。
-/
noncomputable def toStandardFutureMinimumReturnData
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    StandardFutureMinimumReturnData O :=
  { unbounded := D.state.unbounded
    index := D.state.index
    length := D.firstCrossingLength
    crossing := by
      change
        FirstCrossingAt
          O
          D.state.startIndex
          D.firstCrossingLength
      exact D.firstCrossing }


/--
最小 first crossing は exact-adjacent または late。
-/
theorem firstCrossing_exact_or_late
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    D.firstCrossingLength = D.state.length ∨
      D.firstCrossingLength < D.state.length := by
  have hle :=
    D.firstCrossingLength_le_length
  omega

end AdjacentContractingReturnData


namespace AdjacentContractingReturnTowerData

/--
tower の第 `n` 項における最小 first-crossing 長。
-/
noncomputable def firstCrossingLength
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) : ℕ :=
  (T.state n).firstCrossingLength


/--
tower 各項の最小 first crossing。
-/
theorem firstCrossing
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) :
    FirstCrossingAt
      O
      (O.futureMinIndex (T.select n))
      (T.firstCrossingLength n) := by
  change
    FirstCrossingAt
      O
      (T.state n).state.startIndex
      (T.state n).firstCrossingLength
  exact
    (T.state n).firstCrossing


/--
tower 各項で最小 first crossing は adjacent gap 以下。
-/
theorem firstCrossingLength_le_adjacentLength
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) :
    T.firstCrossingLength n ≤
      consecutiveFutureMinimumIndexGap O (T.select n) := by
  change
    (T.state n).firstCrossingLength ≤
      (T.state n).state.length
  exact
    (T.state n).firstCrossingLength_le_length

/--
selected future-minimum 値の発散と bounded first-crossing start bound から、
最小 first-crossing 長は無限大へ進む。
-/
theorem firstCrossingLengths_tend_to_infinity
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      M < T.firstCrossingLength n := by
  intro M
  let S := O.futureMinimumSequence T.unbounded
  obtain ⟨J, hJ⟩ :=
    S.values_eventually_large (M * 3 ^ M)
  refine ⟨J, ?_⟩
  intro n hn
  by_contra hnot
  have hpLe : T.firstCrossingLength n ≤ M :=
    Nat.le_of_not_gt hnot
  have hstartLe :
      O.value (O.futureMinIndex (T.select n)) ≤ M * 3 ^ M := by
    exact futureMinimum_start_le_of_crossingLength_le
      (O.futureMinimumAt_futureMinIndex (T.select n))
      (T.firstCrossing n)
      hpLe
  have hsel : J ≤ T.select n :=
    le_trans hn (T.select_ge n)
  have hlarge0 := hJ (T.select n) hsel
  have hlarge :
      M * 3 ^ M < O.value (O.futureMinIndex (T.select n)) := by
    change M * 3 ^ M < O.value (O.futureMinIndex (T.select n)) at hlarge0
    exact hlarge0
  omega

/-- exact-adjacency となる tower 添字。 -/
def ExactAt
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) : Prop :=
  T.firstCrossingLength n =
    consecutiveFutureMinimumIndexGap O (T.select n)

/-- late-next-minimum となる tower 添字。 -/
def LateAt
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) : Prop :=
  T.firstCrossingLength n <
    consecutiveFutureMinimumIndexGap O (T.select n)

/-- 各 tower 添字は exact または late。 -/
theorem exact_or_late
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) :
    T.ExactAt n ∨ T.LateAt n := by
  unfold ExactAt LateAt
  have hle := T.firstCrossingLength_le_adjacentLength n
  omega

/-- cofinal exact 部分列から旧 ExactAdjacencyTowerData を構成。 -/
noncomputable def toExactAdjacencyTower
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (hExact : Cofinally T.ExactAt) :
    ExactAdjacencyTowerData O := by
  let s := Cofinally.select T.ExactAt hExact
  refine
    { unbounded := T.unbounded
      select := fun j => T.select (s j)
      select_strict := ?_
      length := fun j => T.firstCrossingLength (s j)
      crossing := fun j => T.firstCrossing (s j)
      exact := ?_
      lengths_tend_to_infinity := ?_ }
  · intro a b hab
    exact T.select_strict (Cofinally.select_strict T.ExactAt hExact hab)
  · intro j
    exact Cofinally.select_spec T.ExactAt hExact j
  · intro M
    obtain ⟨J, hJ⟩ := T.firstCrossingLengths_tend_to_infinity M
    refine ⟨J, ?_⟩
    intro j hj
    have hsj : J ≤ s j :=
      le_trans hj (Cofinally.select_ge T.ExactAt hExact j)
    exact hJ (s j) hsj

/-- cofinal late 部分列から旧 LateNextMinimumTowerData を構成。 -/
noncomputable def toLateNextMinimumTower
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (hLate : Cofinally T.LateAt) :
    LateNextMinimumTowerData O := by
  let s := Cofinally.select T.LateAt hLate
  refine
    { unbounded := T.unbounded
      select := fun j => T.select (s j)
      select_strict := ?_
      length := fun j => T.firstCrossingLength (s j)
      crossing := fun j => T.firstCrossing (s j)
      late := ?_
      lengths_tend_to_infinity := ?_ }
  · intro a b hab
    exact T.select_strict (Cofinally.select_strict T.LateAt hLate hab)
  · intro j
    exact Cofinally.select_spec T.LateAt hLate j
  · intro M
    obtain ⟨J, hJ⟩ := T.firstCrossingLengths_tend_to_infinity M
    refine ⟨J, ?_⟩
    intro j hj
    have hsj : J ≤ s j :=
      le_trans hj (Cofinally.select_ge T.LateAt hLate j)
    exact hJ (s j) hsj

/--
Adjacent Contracting tower は旧 ExactAdjacency または LateNextMinimum tower へ
無条件で再接続できる。
-/
theorem toExact_or_Late_tower
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O) :
    Nonempty (ExactAdjacencyTowerData O) ∨
      Nonempty (LateNextMinimumTowerData O) := by
  by_cases hExact : Cofinally T.ExactAt
  · exact Or.inl ⟨T.toExactAdjacencyTower hExact⟩
  · obtain ⟨N, hN⟩ :=
      Cofinally.eventually_not_of_not T.ExactAt hExact
    have hLate : Cofinally T.LateAt := by
      intro M
      let n := max M N
      have hnM : M ≤ n := le_max_left M N
      have hnN : N ≤ n := le_max_right M N
      have hnotExact := hN n hnN
      have hcases := T.exact_or_late n
      rcases hcases with hE | hL
      · exact False.elim (hnotExact hE)
      · exact ⟨n, hnM, hL⟩
    exact Or.inr ⟨T.toLateNextMinimumTower hLate⟩

end AdjacentContractingReturnTowerData

/-- existence-level でも旧 Exact/Late obstruction へ戻せる。 -/
theorem hasExact_or_Late_of_hasAdjacentContracting
    (h : HasAdjacentContractingReturnTower) :
    HasExactAdjacencyTower ∨ HasLateNextMinimumTower := by
  rcases h with ⟨O, ⟨T⟩⟩
  rcases T.toExact_or_Late_tower with hExact | hLate
  · exact Or.inl ⟨O, hExact⟩
  · exact Or.inr ⟨O, hLate⟩

end CollatzSecondLayer3
