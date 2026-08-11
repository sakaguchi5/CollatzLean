import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.FirstOvershootSaturation
import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.NaturalZeroReplayArithmetic

/-!
# natural j=0 coordinate boundedness への最終還元

PositiveReturn canonical chain では十分後の全項に natural `j=0` sign-change packet が存在する。
この packet の arithmetic coordinate を

  `q = n + d`

と置くと、predecessor boundary `S` に対して

  `S + 1 = 4 * q`

が exact に成立する。

一方 `S` は future-minimum start 以後の actual boundary なので

  `startValue <= S`。

さらに canonical chain の start value は chain index とともに狭義増加する。
したがって chain index `k` 自身が start value の下界になり、natural packet の
`q` は chain 上で一様有界にはなれない。

このファイルでは最後に残す仮定を次の非常に弱い命題だけへ切り出す。

  `NaturalZeroReplayCoordinateBounded`

これは「natural `j=0` packet は存在しない」とは仮定せず、packet が何個存在してもよい。
ただし全 packet の `n+d` がある有限値以下に一様に抑えられる、という boundedness だけを仮定する。

この boundedness だけで PositiveReturn canonical chain 全体が排除される。
従って今後 bidirectional decoder 側で示すべき局所整数論命題は、
`NoNaturalZeroReplaySignChange` 全体ではなく、この boundedness だけで十分である。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn

namespace CanonicalChain

/-- chain の start value は隣接項ごとに狭義増加する。 -/
theorem startValue_strict_succ
    {O : OddOrbit} (C : CanonicalChain O) (k : ℕ) :
    (C.state k).startValue < (C.state (k + 1)).startValue := by
  calc
    (C.state k).startValue
        < (C.state k).nextValue :=
      (C.state k).startValue_lt_nextValue
    _ = (C.state (k + 1)).startValue := by
      simpa [CanonicalChain.state] using
        C.core.nextValue_eq_next_startValue k

/-- chain index 自身が start value の厳密下界になる。 -/
theorem index_lt_startValue
    {O : OddOrbit} (C : CanonicalChain O) :
    ∀ k : ℕ, k < (C.state k).startValue := by
  intro k
  induction k with
  | zero =>
      have hpos : 0 < O.value (C.state 0).startIndex :=
        O.value_pos _
      simpa [State.startValue] using hpos
  | succ k ih =>
      have hstep := C.startValue_strict_succ k
      omega

/--
natural packet の coordinate sum `q=n+d` は、その block の actual start を
`4*q` より下へ抑える。
-/
theorem startValue_lt_four_mul_naturalCoordinateSum
    {O : OddOrbit} (C : CanonicalChain O) (k : ℕ)
    (D :
      FirstCrossingData.NaturalZeroReplaySignChangeData
        (C.firstCrossing k)) :
    (C.state k).startValue <
      4 * (D.arithmeticData.n + D.arithmeticData.d) := by
  let F := C.firstCrossing k
  have hstartBoundary :
      (C.state k).startValue ≤
        FirstCrossingData.boundaryValue F D.pred := by
    have h := (C.state k).startFutureMinimum.le_segment_end D.pred
    simpa [F, State.startValue, FirstCrossingData.boundaryValue] using h
  have hboundary :
      FirstCrossingData.boundaryValue F D.pred =
        Word.canonicalStart D.predecessorWord := by
    simpa [F,
      FirstCrossingData.NaturalZeroReplaySignChangeData.predecessorWord]
      using D.predStart_eq
  have hcoord := D.arithmeticData.predecessorStart_add_one
  have hstartAdd :
      (C.state k).startValue + 1 ≤
        4 * (D.arithmeticData.n + D.arithmeticData.d) := by
    calc
      (C.state k).startValue + 1
          ≤ FirstCrossingData.boundaryValue F D.pred + 1 :=
        Nat.add_le_add_right hstartBoundary 1
      _ = Word.canonicalStart D.predecessorWord + 1 := by
        rw [hboundary]
      _ = 4 * (D.arithmeticData.n + D.arithmeticData.d) := hcoord
  omega

/--
PositiveReturn canonical chain 上では natural `j=0` packet の coordinate sum `n+d` は
任意に大きくなる。

これは gap-depth や common-prefix frequency を使わず、
* sufficiently late な全項に natural packet が存在すること
* chain start が狭義増加すること
* `S+1=4*(n+d)`
だけから従う。
-/
theorem naturalZeroReplayCoordinateSum_unbounded
    {O : OddOrbit} (C : CanonicalChain O) :
    ∀ Q : ℕ,
      ∃ k : ℕ,
      ∃ D :
        FirstCrossingData.NaturalZeroReplaySignChangeData
          (C.firstCrossing k),
        Q < D.arithmeticData.n + D.arithmeticData.d := by
  intro Q
  obtain ⟨J, hJ⟩ := C.eventually_naturalZeroReplaySignChange
  let k := J + 4 * Q + 1
  have hkJ : J ≤ k := by
    dsimp [k]
    omega
  obtain ⟨D⟩ := hJ k hkJ
  have hindex := C.index_lt_startValue k
  have hcoord := C.startValue_lt_four_mul_naturalCoordinateSum k D
  have hkLarge : 4 * Q < k := by
    dsimp [k]
    omega
  refine ⟨k, D, ?_⟩
  omega

end CanonicalChain

/--
唯一残す弱い局所整数論仮定。

natural `j=0` sign-change packet 自体の不存在は要求しない。
存在する全 packet について、coordinate sum `n+d` がある有限上界を持つことだけを要求する。

bidirectional decoder で今後閉じるべき target はこの boundedness だけで十分である。
-/
def NaturalZeroReplayCoordinateBounded : Prop :=
  ∃ Q : ℕ,
    ∀ {O : OddOrbit} {R : State O}
      (F : FirstCrossingData R)
      (D : FirstCrossingData.NaturalZeroReplaySignChangeData F),
      D.arithmeticData.n + D.arithmeticData.d ≤ Q

/--
旧 target `NoNaturalZeroReplaySignChange` は新 boundedness target より強い。
従って今回切り出した仮定が確かに弱化になっていることを Lean 上で明示する。
-/
theorem naturalZeroReplayCoordinateBounded_of_noNaturalZeroReplaySignChange
    (hNo : NoNaturalZeroReplaySignChange) :
    NaturalZeroReplayCoordinateBounded := by
  refine ⟨0, ?_⟩
  intro O R F D
  exact False.elim (hNo F D)

/--
`n+d` の一様有界性だけで PositiveReturn canonical chain は存在できない。

十分後の全 chain 項から natural packet を取り、その coordinate sum が任意に大きくなる
定理と boundedness を直接衝突させる。
-/
theorem no_canonicalChain_of_naturalZeroReplayCoordinateBounded
    (hBound : NaturalZeroReplayCoordinateBounded) :
    ¬ HasCanonicalChain := by
  rintro ⟨O, ⟨C⟩⟩
  obtain ⟨Q, hQ⟩ := hBound
  obtain ⟨k, D, hlarge⟩ :=
    C.naturalZeroReplayCoordinateSum_unbounded Q
  have hsmall := hQ (C.firstCrossing k) D
  omega

end PositiveReturn
end AdjacentReturn
end Collatz
