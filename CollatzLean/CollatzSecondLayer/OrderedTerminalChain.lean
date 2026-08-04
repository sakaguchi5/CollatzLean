import CollatzLean.CollatzSecondLayer.CoherentCylinders
import CollatzLean.CollatzSecondLayer.CylinderConsequences
import CollatzLean.CollatzSecondLayer.TwoAdicDifference

/-!
# 隣接ordered terminal chain

整合したfuture-minimum cylinder列から十分疎な部分列を選び、固定baseから
各cylinder終点までのprefixと、隣接終点間のsuffixを一つのterminal pairにする。
これにより、独立packet列では失われていた

`YAR n = YA (n+1)`

を定義上保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- 隣接する二区間のsegment wordは全区間のsegment wordになる。 -/
theorem segmentWord_add
    (O : OddOrbit)
    (i m n : ℕ) :
    O.segmentWord i (m + n) =
      O.segmentWord i m ++ O.segmentWord (i + m) n := by
  induction m generalizing i with
  | zero =>
      simp
  | succ m ih =>
      have hlength :
          m + 1 + n = (m + n) + 1 := by
        omega
      have hindex :
          i + 1 + m = i + (m + 1) := by
        omega
      rw [hlength]
      rw [segmentWord_succ]
      rw [segmentWord_succ, List.cons_append]
      rw [ih (i := i + 1)]
      rw [hindex]

end OddOrbit

/-- 固定baseから見た、一つの選択済みcylinder終点。 -/
structure ChainEndpointNode
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) where
  sourceIndex : ℕ
  returnDepth : ℕ
  returnOddPart : ℕ
  returnDepth_pos : 0 < returnDepth
  returnOddPart_odd : Odd returnOddPart
  return_eq :
    S.finishValue sourceIndex =
      O.value 0 + 2 ^ returnDepth * returnOddPart

namespace ChainEndpointNode

/-- nodeのcylinder開始位置。 -/
def startPosition
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (N : ChainEndpointNode S) : ℕ :=
  S.startPosition N.sourceIndex

/-- nodeのcylinder終点位置。 -/
def finishPosition
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (N : ChainEndpointNode S) : ℕ :=
  S.finishPosition N.sourceIndex

/-- nodeのcylinder開始値。 -/
def startValue
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (N : ChainEndpointNode S) : ℕ :=
  S.startValue N.sourceIndex

/-- nodeのcylinder終点値。 -/
def finishValue
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (N : ChainEndpointNode S) : ℕ :=
  S.finishValue N.sourceIndex

/-- nodeの元cylinder長。 -/
def cylinderLength
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (N : ChainEndpointNode S) : ℕ :=
  S.length N.sourceIndex

/-- nodeの終点は固定baseより大きい。 -/
theorem base_lt_finishValue
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (N : ChainEndpointNode S) :
    O.value 0 < N.finishValue := by
  change O.value 0 < S.finishValue N.sourceIndex
  rw [N.return_eq]
  apply Nat.lt_add_of_pos_right
  exact Nat.mul_pos
    (Nat.pow_pos (by omega))
    (by
      rcases N.returnOddPart_odd with ⟨k, hk⟩
      omega)

/-- 開始値が固定baseを越えるcylinderからendpoint nodeを作る。 -/
noncomputable def ofIndex
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ)
    (hbase : O.value 0 < S.startValue j) :
    ChainEndpointNode S := by
  have hfinish :
      O.value 0 < S.finishValue j :=
    lt_of_lt_of_le
      hbase
      (S.startValue_le_finishValue j)
  have hex :
      ∃ d u : ℕ,
        0 < d ∧
        O.value (S.finishPosition j) =
          O.value 0 + 2 ^ d * u ∧
        Odd u := by
    exact
      exists_positive_exactTwoFactor_of_odd_lt
        (O.value_odd 0)
        (O.value_odd (S.finishPosition j))
        hfinish
  let d : ℕ :=
    Classical.choose hex
  have hdSpec :
      ∃ u : ℕ,
        0 < d ∧
        O.value (S.finishPosition j) =
          O.value 0 + 2 ^ d * u ∧
        Odd u := by
    simpa [d] using Classical.choose_spec hex
  let u : ℕ :=
    Classical.choose hdSpec
  have hSpec :
      0 < d ∧
      O.value (S.finishPosition j) =
        O.value 0 + 2 ^ d * u ∧
      Odd u := by
    simpa [u] using Classical.choose_spec hdSpec
  exact
    { sourceIndex := j
      returnDepth := d
      returnOddPart := u
      returnDepth_pos := hSpec.1
      returnOddPart_odd := hSpec.2.2
      return_eq := by
        simpa [
          finishValue,
          CoherentC3CylinderSequence.finishValue
        ] using hSpec.2.1 }

end ChainEndpointNode

namespace CoherentC3CylinderSequence

/-- chainの最初のendpoint node。 -/
noncomputable def firstEndpointNode
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    ChainEndpointNode S := by
  let hex :=
    S.exists_later_startValue (O.value 0) 0
  let j : ℕ :=
    Classical.choose hex
  exact ChainEndpointNode.ofIndex S j
    (Classical.choose_spec hex).2

/--
`ofIndex`で構成したendpoint nodeの`sourceIndex`は、
構成時に指定したcylinder index `j`そのものである。

`ofIndex`から作ったnodeの開始位置・開始値などを、
元のcylinder indexに戻して書き換えるためのsimp補題。
-/
@[simp]
theorem ofIndex_sourceIndex
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ)
    (hbase : O.value 0 < S.startValue j) :
    (ChainEndpointNode.ofIndex S j hbase).sourceIndex = j := by
  rfl

/--
現在nodeより十分後ろにあり、開始値も現在終点を越える次nodeが存在する。
位置には`2*finishPosition + returnDepth + 1`を要求し、long suffixと
terminal alpha gapを同時に確保する。
-/
theorem exists_nextEndpointNode
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (N : ChainEndpointNode S) :
    ∃ N' : ChainEndpointNode S,
      N.sourceIndex < N'.sourceIndex ∧
      2 * N.finishPosition + N.returnDepth + 1 < N'.startPosition ∧
      N.finishValue < N'.startValue := by
  obtain ⟨j, hindex, hposition, hvalue⟩ :=
    S.exists_strictly_later_cylinder
      N.sourceIndex
      (2 * N.finishPosition + N.returnDepth + 1)
      N.finishValue
  have hbase : O.value 0 < S.startValue j :=
    lt_trans N.base_lt_finishValue hvalue
  let N' := ChainEndpointNode.ofIndex S j hbase
  refine ⟨N', ?_, ?_, ?_⟩
  · simpa [N'] using hindex
  · simpa [N', ChainEndpointNode.startPosition] using hposition
  · simpa [N', ChainEndpointNode.startValue] using hvalue

/-- 古典選択した次endpoint node。 -/
noncomputable def nextEndpointNode
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (N : ChainEndpointNode S) :
    ChainEndpointNode S :=
  Classical.choose (S.exists_nextEndpointNode N)

/-- 選択した次nodeの三条件。 -/
theorem nextEndpointNode_spec
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (N : ChainEndpointNode S) :
    N.sourceIndex < (S.nextEndpointNode N).sourceIndex ∧
    2 * N.finishPosition + N.returnDepth + 1 <
      (S.nextEndpointNode N).startPosition ∧
    N.finishValue < (S.nextEndpointNode N).startValue :=
  Classical.choose_spec (S.exists_nextEndpointNode N)

/-- 疎に選ばれた無限endpoint node列。 -/
noncomputable def endpointNode
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    ℕ → ChainEndpointNode S
  | 0 => S.firstEndpointNode
  | n + 1 => S.nextEndpointNode (S.endpointNode n)

/-- node添字は一段ごとに真に増える。 -/
theorem endpointNode_sourceIndex_lt_succ
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (S.endpointNode n).sourceIndex <
      (S.endpointNode (n + 1)).sourceIndex := by
  simpa [endpointNode] using
    (S.nextEndpointNode_spec (S.endpointNode n)).1

/-- node添字列は狭義単調。 -/
theorem endpointNode_sourceIndex_strict
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    StrictMono (fun n => (S.endpointNode n).sourceIndex) :=
  strictMono_nat_of_lt_succ S.endpointNode_sourceIndex_lt_succ

/-- 次nodeの開始位置は現在nodeの終点より十分後ろ。 -/
theorem endpointNode_position_bound
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    2 * (S.endpointNode n).finishPosition +
        (S.endpointNode n).returnDepth + 1 <
      (S.endpointNode (n + 1)).startPosition := by
  simpa [endpointNode] using
    (S.nextEndpointNode_spec (S.endpointNode n)).2.1

/-- 次nodeの開始値は現在nodeの終点より大きい。 -/
theorem endpointNode_finish_lt_next_start
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (S.endpointNode n).finishValue <
      (S.endpointNode (n + 1)).startValue := by
  simpa [endpointNode] using
    (S.nextEndpointNode_spec (S.endpointNode n)).2.2

/-- node終点値列は狭義単調。 -/
theorem endpointNode_finishValue_lt_succ
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (S.endpointNode n).finishValue <
      (S.endpointNode (n + 1)).finishValue :=
  lt_of_lt_of_le
    (S.endpointNode_finish_lt_next_start n)
    (S.startValue_le_finishValue
      (S.endpointNode (n + 1)).sourceIndex)

/-- node終点位置列は狭義単調。 -/
theorem endpointNode_finishPosition_lt_succ
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (S.endpointNode n).finishPosition <
      (S.endpointNode (n + 1)).finishPosition := by
  have hbound := S.endpointNode_position_bound n
  have hlen := S.length_pos (S.endpointNode (n + 1)).sourceIndex
  dsimp [ChainEndpointNode.startPosition,
    ChainEndpointNode.finishPosition,
    CoherentC3CylinderSequence.finishPosition] at hbound ⊢
  omega

end CoherentC3CylinderSequence

/- 一つの隣接terminal pairを作るための補助定義。 -/
namespace OrderedTerminalPair

noncomputable def A
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) : ExpWord :=
  O.segmentWord 0 (S.endpointNode n).finishPosition

noncomputable def R
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) : ExpWord :=
  O.segmentWord
    (S.endpointNode n).finishPosition
    ((S.endpointNode (n + 1)).finishPosition -
      (S.endpointNode n).finishPosition)

/-- chain pairのsuffix長。 -/
noncomputable def suffixLength
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) : ℕ :=
  (S.endpointNode (n + 1)).finishPosition -
    (S.endpointNode n).finishPosition

@[simp] theorem A_length
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (A S n).length = (S.endpointNode n).finishPosition := by
  simp [A]

@[simp] theorem R_length
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (R S n).length = suffixLength S n := by
  simp [R, suffixLength]

/-- suffixは非空。 -/
theorem suffixLength_pos
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    0 < suffixLength S n := by
  unfold suffixLength
  exact Nat.sub_pos_of_lt (S.endpointNode_finishPosition_lt_succ n)

/-- suffix長は現在return depthより大きい。 -/
theorem returnDepth_lt_suffixLength
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (S.endpointNode n).returnDepth < suffixLength S n := by
  have hbound := S.endpointNode_position_bound n
  have hnextLen := S.length_pos (S.endpointNode (n + 1)).sourceIndex
  unfold suffixLength
  dsimp [ChainEndpointNode.startPosition,
    ChainEndpointNode.finishPosition,
    CoherentC3CylinderSequence.finishPosition] at hbound ⊢
  omega

/-- prefix長はsuffix長以下。 -/
theorem prefixLength_le_suffixLength
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (A S n).length ≤ (R S n).length := by
  rw [A_length, R_length]
  have hbound := S.endpointNode_position_bound n
  have hnextLen := S.length_pos (S.endpointNode (n + 1)).sourceIndex
  unfold suffixLength
  dsimp [ChainEndpointNode.startPosition,
    ChainEndpointNode.finishPosition,
    CoherentC3CylinderSequence.finishPosition] at hbound ⊢
  omega

/-- chain pairの前半run。 -/
theorem runA
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    Runs (A S n)
      (O.value 0)
      (S.endpointNode n).finishValue := by
  simpa [
    A,
    ChainEndpointNode.finishValue,
    ChainEndpointNode.finishPosition,
    CoherentC3CylinderSequence.finishValue
  ] using
    O.runs_segment 0 (S.endpointNode n).finishPosition

/-- chain pairのsuffix run。 -/
theorem runR
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    Runs (R S n)
      (S.endpointNode n).finishValue
      (S.endpointNode (n + 1)).finishValue := by
  have hpos :
      (S.endpointNode n).finishPosition <
        (S.endpointNode (n + 1)).finishPosition :=
    S.endpointNode_finishPosition_lt_succ n
  have hend :
      (S.endpointNode n).finishPosition + suffixLength S n =
        (S.endpointNode (n + 1)).finishPosition := by
    unfold suffixLength
    exact Nat.add_sub_of_le (Nat.le_of_lt hpos)
  have hrun :=
    O.runs_segment
      (S.endpointNode n).finishPosition
      (suffixLength S n)
  rw [hend] at hrun
  change
    Runs
      (O.segmentWord
        (S.endpointNode n).finishPosition
        (suffixLength S n))
      (O.value (S.endpointNode n).finishPosition)
      (O.value (S.endpointNode (n + 1)).finishPosition)
  exact hrun

/-- suffixの総2除算数は現在return depthより大きい。 -/
theorem returnDepth_lt_twoSteps_R
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (S.endpointNode n).returnDepth < twoSteps (R S n) := by
  have hvalid := (runR S n).valid
  have hlength :
      (R S n).length ≤ twoSteps (R S n) := by
    simpa [oddSteps] using oddSteps_le_twoSteps hvalid
  have hsuffixLength :
      suffixLength S n ≤ twoSteps (R S n) := by
    simpa [suffixLength] using hlength
  exact lt_of_lt_of_le
    (returnDepth_lt_suffixLength S n)
    hsuffixLength

/-- 隣接endpointから`TerminalPairData`を構成する。 -/
noncomputable def pair
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    TerminalPairData := by
  let N := S.endpointNode n
  let N' := S.endpointNode (n + 1)
  let gap :=
    twoSteps (R S n) +
      N'.returnDepth -
      N.returnDepth
  have hdepth :
      N.returnDepth <
        twoSteps (R S n) :=
    returnDepth_lt_twoSteps_R S n
  have hfinishPositionPos :
      0 < N.finishPosition := by
    have hlen :
        0 < S.length N.sourceIndex :=
      S.length_pos N.sourceIndex
    change
      0 <
        S.startPosition N.sourceIndex +
          S.length N.sourceIndex
    omega
  exact
    { A := A S n
      R := R S n
      X := O.value 0
      YA := N.finishValue
      YAR := N'.finishValue
      lambdaA := N.returnDepth
      lambdaAR := N'.returnDepth
      uA := N.returnOddPart
      uAR := N'.returnOddPart
      gap := gap

      runA := runA S n
      runR := runR S n

      returnA :=
        ⟨N.return_eq, N.returnOddPart_odd⟩

      returnAR :=
        ⟨N'.return_eq, N'.returnOddPart_odd⟩

      alpha_gap := by
        unfold alpha
        rw [twoSteps_append]
        dsimp [gap]
        omega

      gap_pos := by
        dsimp [gap]
        omega

      A_nonempty := by
        intro hnil
        have hzero :
            (A S n).length = 0 := by
          simpa using congrArg List.length hnil
        rw [A_length] at hzero
        have hpos :
            0 < (S.endpointNode n).finishPosition := by
          simpa [N] using hfinishPositionPos
        exact (Nat.ne_of_gt hpos) hzero
      R_nonempty := by
        intro hnil
        have hzero :
            (R S n).length = 0 := by
          have h :=
            congrArg List.length hnil
          simpa using h
        have hRlength :
            (R S n).length =
              suffixLength S n :=
          R_length S n
        have hsuffixPos :
            0 < suffixLength S n :=
          suffixLength_pos S n
        omega }

/-- chain pairの二終点は正順序。 -/
theorem pair_value_lt
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (pair S n).YA < (pair S n).YAR := by
  exact S.endpointNode_finishValue_lt_succ n

/-- chain pairの正の完全差分。 -/
noncomputable def ordered
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    OrderedDifferenceData (pair S n) :=
  orderedDifferenceDataOfLt (pair S n) (pair_value_lt S n)

end OrderedTerminalPair

/--
整合cylinder列から得られる一本の隣接ordered terminal chain。
-/
structure InfiniteOrderedTerminalChain
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) where
  pair : ℕ → TerminalPairData
  ordered : ∀ n : ℕ, OrderedDifferenceData (pair n)
  sourceIndex : ℕ → ℕ
  sourceIndex_strict : StrictMono sourceIndex
  endpointPosition : ℕ → ℕ
  endpointPosition_strict : StrictMono endpointPosition
  lowerEndpointValue : ∀ n : ℕ,
    O.value (endpointPosition n) = (pair n).YA
  upperEndpointValue : ∀ n : ℕ,
    O.value (endpointPosition (n + 1)) = (pair n).YAR
  sourceFinish : ∀ n : ℕ,
    (pair n).YAR = S.finishValue (sourceIndex (n + 1))
  adjacent : ∀ n : ℕ,
    (pair n).YAR = (pair (n + 1)).YA
  prefixGrowth : ∀ n : ℕ,
    (pair (n + 1)).A = (pair n).A ++ (pair n).R
  longSuffix : ∀ n : ℕ,
    (pair n).A.length ≤ (pair n).R.length
  targetCylinderInside : ∀ n : ℕ,
    S.length (sourceIndex (n + 1)) ≤ (pair n).R.length
  endpointPolynomialK : ℕ
  endpointPolynomialA : ℕ
  endpointPolynomial : ∀ n : ℕ,
    (pair n).YAR ≤
      endpointPolynomialK * ((pair n).R.length + 1) ^ endpointPolynomialA

namespace InfiniteOrderedTerminalChain

/--
整合cylinder列の終点に対する、一様な多項式上界の証人。

`finishes_polynomialSmall`が与える存在証明を、
後続の構造体へ格納できるデータとして取り出す。
-/
structure EndpointPolynomialWitness
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) where
  K : ℕ
  A : ℕ
  bound : ∀ j : ℕ,
    S.finishValue j ≤ K * (S.length j + 1) ^ A


/--
整合cylinder列の終点に対する多項式上界を、
古典選択によって明示的な証人へ変換する。
-/
noncomputable def endpointPolynomialWitness
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    EndpointPolynomialWitness S := by
  have hex :
      ∃ K A : ℕ, ∀ j : ℕ,
        S.finishValue j ≤
          K * (S.length j + 1) ^ A :=
    finishes_polynomialSmall S
  let K : ℕ :=
    Classical.choose hex
  have hK :
      ∃ A : ℕ, ∀ j : ℕ,
        S.finishValue j ≤
          K * (S.length j + 1) ^ A := by
    simpa [K] using Classical.choose_spec hex
  let A : ℕ :=
    Classical.choose hK
  have hbound :
      ∀ j : ℕ,
        S.finishValue j ≤
          K * (S.length j + 1) ^ A := by
    simpa [A] using Classical.choose_spec hK
  exact
    { K := K
      A := A
      bound := hbound }

/--
隣接endpointから作られる次のterminal pairのprefixは、
現在のprefixとsuffixの連結に等しい。
-/
theorem orderedPair_prefixGrowth
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    (OrderedTerminalPair.pair S (n + 1)).A =
      (OrderedTerminalPair.pair S n).A ++
        (OrderedTerminalPair.pair S n).R := by
  let p : ℕ :=
    (S.endpointNode n).finishPosition
  let q : ℕ :=
    (S.endpointNode (n + 1)).finishPosition
  have hpq : p ≤ q :=
    Nat.le_of_lt
      (S.endpointNode_finishPosition_lt_succ n)
  have hadd :
      p + (q - p) = q := by
    exact Nat.add_sub_of_le hpq
  change
    O.segmentWord 0 q =
      O.segmentWord 0 p ++
        O.segmentWord p (q - p)
  calc
    O.segmentWord 0 q
        = O.segmentWord 0 (p + (q - p)) := by
            rw [hadd]
    _ = O.segmentWord 0 p ++
          O.segmentWord p (q - p) := by
            simpa using
              O.segmentWord_add 0 p (q - p)


/--
次endpointに対応するtarget cylinderの語長は、
現在endpointから次endpointまでのsuffix長以下である。
-/
theorem orderedPair_targetCylinderInside
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (n : ℕ) :
    S.length
        (S.endpointNode (n + 1)).sourceIndex ≤
      (OrderedTerminalPair.pair S n).R.length := by
  have hstart :=
    S.endpointNode_position_bound n
  have hfinishPosition :
      (S.endpointNode (n + 1)).finishPosition =
        (S.endpointNode (n + 1)).startPosition +
          S.length
            (S.endpointNode (n + 1)).sourceIndex := by
    rfl
  change
    S.length
        (S.endpointNode (n + 1)).sourceIndex ≤
      (OrderedTerminalPair.R S n).length
  rw [OrderedTerminalPair.R_length]
  unfold OrderedTerminalPair.suffixLength
  rw [hfinishPosition]
  omega


/--
隣接terminal pairの上側終点は、
そのsuffix長に対して一様に多項式小である。
-/
theorem orderedPair_endpointPolynomial
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (W : EndpointPolynomialWitness S)
    (n : ℕ) :
    (OrderedTerminalPair.pair S n).YAR ≤
      W.K *
        ((OrderedTerminalPair.pair S n).R.length + 1) ^ W.A := by
  let j : ℕ :=
    (S.endpointNode (n + 1)).sourceIndex
  have hsmall :
      S.finishValue j ≤
        W.K * (S.length j + 1) ^ W.A :=
    W.bound j
  have hinside :
      S.length j ≤
        (OrderedTerminalPair.pair S n).R.length := by
    simpa [j] using
      orderedPair_targetCylinderInside S n
  have hpow :
      (S.length j + 1) ^ W.A ≤
        ((OrderedTerminalPair.pair S n).R.length + 1) ^ W.A := by
    gcongr
  have hmul :
      W.K * (S.length j + 1) ^ W.A ≤
        W.K *
          ((OrderedTerminalPair.pair S n).R.length + 1) ^ W.A := by
    exact Nat.mul_le_mul_left W.K hpow
  have hsmall' :
      S.finishValue
          (S.endpointNode (n + 1)).sourceIndex ≤
        W.K *
          (S.length
              (S.endpointNode (n + 1)).sourceIndex + 1) ^ W.A := by
    simpa [j] using hsmall
  change
    S.finishValue
        (S.endpointNode (n + 1)).sourceIndex ≤
      W.K *
        ((OrderedTerminalPair.pair S n).R.length + 1) ^ W.A
  exact hsmall'.trans hmul


/--
整合cylinder列から隣接ordered terminal chainを構成する。
-/
noncomputable def ofCoherent
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    InfiniteOrderedTerminalChain S := by
  let W : EndpointPolynomialWitness S :=
    endpointPolynomialWitness S
  refine
    { pair :=
        OrderedTerminalPair.pair S

      ordered :=
        OrderedTerminalPair.ordered S

      sourceIndex :=
        fun n => (S.endpointNode n).sourceIndex

      sourceIndex_strict :=
        S.endpointNode_sourceIndex_strict

      endpointPosition :=
        fun n => (S.endpointNode n).finishPosition

      endpointPosition_strict :=
        strictMono_nat_of_lt_succ
          S.endpointNode_finishPosition_lt_succ

      lowerEndpointValue := by
        intro n
        rfl

      upperEndpointValue := by
        intro n
        rfl

      sourceFinish := by
        intro n
        rfl

      adjacent := by
        intro n
        rfl

      prefixGrowth :=
        orderedPair_prefixGrowth S

      longSuffix :=
        OrderedTerminalPair.prefixLength_le_suffixLength S

      targetCylinderInside :=
        orderedPair_targetCylinderInside S

      endpointPolynomialK :=
        W.K

      endpointPolynomialA :=
        W.A

      endpointPolynomial :=
        orderedPair_endpointPolynomial S W }

end InfiniteOrderedTerminalChain

end CollatzSecondLayer
