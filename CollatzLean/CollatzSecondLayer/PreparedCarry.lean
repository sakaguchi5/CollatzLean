import CollatzLean.CollatzSecondLayer.InfiniteTerminal
import CollatzLean.CollatzFirstLayer.CarrySynchronization
import CollatzLean.CollatzFirstLayer.DownwardReplay

/-!
# ordered terminal差分からprepared carryまで

terminal pairの二終点が増加順にあるとき、その差を完全2進分解し、下側値が
実軌道上に埋め込まれていることから、累積2除算数が元差深さへ初めて到達する
同期prefixを選ぶ。同期prefixの上下runと残り差深さを由来付きで保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- terminal pairの二終点間にある正の完全2進差分。 -/
structure OrderedDifferenceData (T : TerminalPairData) where
  depth : ℕ
  oddPart : ℕ
  depth_pos : 0 < depth
  difference : T.YAR = T.YA + 2 ^ depth * oddPart
  oddPart_odd : Odd oddPart

namespace OrderedDifferenceData

/-- ordered差分では下側終点が上側終点より真に小さい。 -/
theorem value_lt
    {T : TerminalPairData}
    (D : OrderedDifferenceData T) :
    T.YA < T.YAR := by
  rw [D.difference]
  apply Nat.lt_add_of_pos_right
  apply Nat.mul_pos
  · exact Nat.pow_pos (by omega)
  · rcases D.oddPart_odd with ⟨k, hk⟩
    omega

/-- 完全差分の主2冪は実際の値差以下。 -/
theorem twoPow_le_difference
    {T : TerminalPairData}
    (D : OrderedDifferenceData T) :
    2 ^ D.depth ≤ T.YAR - T.YA := by
  rw [D.difference]
  simp only [Nat.add_sub_cancel_left]
  have hoddPart_one :
      1 ≤ D.oddPart := by
    rcases D.oddPart_odd with ⟨k, hk⟩
    rw [hk]
    omega
  simpa using
    Nat.mul_le_mul_left
      (2 ^ D.depth)
      hoddPart_one

end OrderedDifferenceData

/-- terminal pairの下側終点が無限odd-only軌道上のどの位置にあるか。 -/
structure TerminalLowerOrbitEmbedding
    (O : OddOrbit) (T : TerminalPairData) where
  index : ℕ
  value_eq : O.value index = T.YA

/--
無限terminal抽出のsource cylinderから、`YA`が実軌道上に現れる位置を導出する。
追加の軌道埋込み仮定は不要である。
-/
def terminalLowerOrbitEmbeddingOfExtraction
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    (E : InfiniteTerminalExtraction S)
    (n : ℕ) :
    TerminalLowerOrbitEmbedding O (E.pair n) := by
  let C := S.cylinder (E.sourceIndex n)
  let B := C.toFirstCrossingCylinder
  let i := B.limit.minima.index B.sequenceIndex
  have htotal :
      (E.pair n).A ++ (E.pair n).R =
        O.segmentWord i B.length := by
    simpa [C, B, i, CanonicalC3Cylinder.snapshot,
      FirstCrossingCylinder.word] using E.sourceRelation n
  have hlenEq := congrArg List.length htotal
  have hlen : (E.pair n).A.length ≤ B.length := by
    simp at hlenEq
    omega
  have hprefix :
      O.segmentWord i (E.pair n).A.length = (E.pair n).A := by
    calc
      O.segmentWord i (E.pair n).A.length
          = (O.segmentWord i B.length).take (E.pair n).A.length := by
              symm
              exact O.segmentWord_take_of_le hlen
      _ = ((E.pair n).A ++ (E.pair n).R).take
            (E.pair n).A.length := by rw [← htotal]
      _ = (E.pair n).A := by simp
  have hstart : O.value i = (E.pair n).X := by
    have hs := (E.sourceStart n).symm
    simpa [C, B, i, CanonicalC3Cylinder.snapshot,
      FirstCrossingCylinder.start] using hs
  have hOrbit :
      Runs (E.pair n).A (E.pair n).X
        (O.value (i + (E.pair n).A.length)) := by
    have hrun := O.runs_segment i (E.pair n).A.length
    rw [hprefix] at hrun
    simpa [hstart] using hrun
  have hend :
      O.value (i + (E.pair n).A.length) = (E.pair n).YA :=
    hOrbit.end_unique (E.pair n).runA
  exact ⟨i + (E.pair n).A.length, hend⟩

namespace OddOrbit

/-- 区間語を末尾へ一文字伸ばしたときの総2除算数。 -/
theorem segmentWord_twoSteps_succ_last
    (O : OddOrbit) (i k : ℕ) :
    twoSteps (O.segmentWord i (k + 1)) =
      twoSteps (O.segmentWord i k) + O.exponent (i + k) := by
  induction k generalizing i with
  | zero =>
      simp [OddOrbit.segmentWord, twoSteps]
  | succ k ih =>
      change
        O.exponent i +
            twoSteps (O.segmentWord (i + 1) (k + 1)) =
          (O.exponent i +
              twoSteps (O.segmentWord (i + 1) k)) +
            O.exponent (i + (k + 1))
      rw [ih (i := i + 1)]
      have hindex :
          i + 1 + k = i + (k + 1) := by
        omega
      rw [hindex]
      exact (Nat.add_assoc
        (O.exponent i)
        (twoSteps (O.segmentWord (i + 1) k))
        (O.exponent (i + (k + 1)))).symm

end OddOrbit

/-- 元差深さへ初めて到達する直前までの同期prefix。 -/
structure SynchronizationBoundaryData
    (O : OddOrbit)
    (T : TerminalPairData)
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) where
  length : ℕ
  word : ExpWord
  word_eq : word = O.segmentWord L.index length
  lowerFinish : ℕ
  lowerRun : Runs word T.YA lowerFinish
  consumed_lt : twoSteps word < D.depth
  nextExponent : ℕ
  nextOddPart : ℕ
  nextExponent_eq : nextExponent = O.exponent (L.index + length)
  lowerNextFactorization :
    3 * lowerFinish + 1 = 2 ^ nextExponent * nextOddPart
  lowerNextOdd : Odd nextOddPart
  remaining_le_next : D.depth - twoSteps word ≤ nextExponent

/--
任意の下側軌道埋め込みについて、
総2除算数がordered差分の深さ以上になる有限区間が存在する。
-/
theorem synchronizationBoundary_exists
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    ∃ k : ℕ,
      D.depth ≤
        twoSteps (O.segmentWord L.index (k + 1)) := by
  refine ⟨D.depth, ?_⟩
  have hvalid :=
    (O.runs_segment L.index (D.depth + 1)).valid
  have hlen :=
    oddSteps_le_twoSteps hvalid
  have hsteps :
      D.depth + 1 ≤
        twoSteps
          (O.segmentWord L.index (D.depth + 1)) := by
    simpa [oddSteps] using hlen
  exact le_trans (Nat.le_succ D.depth) hsteps


/--
ordered差分の深さへ初めて到達する直前の区間長。

長さ`k + 1`の区間では総2除算数が`D.depth`以上となり、
長さ`k`の区間ではまだ`D.depth`未満である。
-/
noncomputable def synchronizationBoundaryLength
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    ℕ :=
  Nat.find (synchronizationBoundary_exists D L)


/--
同期境界を一文字越えた区間では、
総2除算数がordered差分の深さ以上になる。
-/
theorem synchronizationBoundaryLength_spec
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    D.depth ≤
      twoSteps
        (O.segmentWord
          L.index
          (synchronizationBoundaryLength D L + 1)) := by
  unfold synchronizationBoundaryLength
  exact Nat.find_spec (synchronizationBoundary_exists D L)


/--
同期境界そのものでは、
消費済みの総2除算数はordered差分の深さより真に小さい。
-/
theorem synchronizationBoundaryLength_consumed_lt
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    twoSteps
        (O.segmentWord
          L.index
          (synchronizationBoundaryLength D L)) <
      D.depth := by
  unfold synchronizationBoundaryLength
  cases hk :
      Nat.find (synchronizationBoundary_exists D L) with
  | zero =>
      simpa [OddOrbit.segmentWord, twoSteps] using D.depth_pos
  | succ m =>
      have hmLt :
          m <
            Nat.find
              (synchronizationBoundary_exists D L) := by
        omega
      have hnot :
          ¬ D.depth ≤
            twoSteps
              (O.segmentWord L.index (m + 1)) := by
        exact
          Nat.find_min
            (synchronizationBoundary_exists D L)
            hmLt
      exact Nat.lt_of_not_ge hnot


/--
同期境界でまだ消費されていない2進深さは、
境界直後の指数以下である。
-/
theorem synchronizationBoundaryLength_remaining_le_next
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    D.depth -
          twoSteps
            (O.segmentWord
              L.index
              (synchronizationBoundaryLength D L))
      ≤
        O.exponent
          (L.index + synchronizationBoundaryLength D L) := by
  have hsum :
      D.depth ≤
        twoSteps
            (O.segmentWord
              L.index
              (synchronizationBoundaryLength D L))
          +
        O.exponent
          (L.index + synchronizationBoundaryLength D L) := by
    have hs :=
      synchronizationBoundaryLength_spec D L
    rw [O.segmentWord_twoSteps_succ_last] at hs
    exact hs
  omega


/--
無限軌道上の下側値から、最小同期境界を古典選択で構成する。
-/
noncomputable def synchronizationBoundaryOfOrbit
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    SynchronizationBoundaryData O T D L := by
  let k : ℕ :=
    synchronizationBoundaryLength D L
  let w : ExpWord :=
    O.segmentWord L.index k
  let z : ℕ :=
    O.value (L.index + k)
  have hkBefore :
      twoSteps (O.segmentWord L.index k) <
        D.depth := by
    simpa [k] using
      synchronizationBoundaryLength_consumed_lt D L
  have hrun0 :
      Runs w (O.value L.index) z := by
    simpa [w, z] using
      O.runs_segment L.index k
  have hrun :
      Runs w T.YA z := by
    simpa [L.value_eq] using hrun0
  let e : ℕ :=
    O.exponent (L.index + k)
  let a : ℕ :=
    O.value (L.index + k + 1)
  have hfactor :
      3 * z + 1 = 2 ^ e * a := by
    dsimp [z, e, a]
    exact (O.step (L.index + k)).symm
  have hremaining :
      D.depth - twoSteps w ≤ e := by
    simpa [k, w, e] using
      synchronizationBoundaryLength_remaining_le_next D L
  exact
    { length := k
      word := w
      word_eq := rfl

      lowerFinish := z
      lowerRun := hrun

      consumed_lt := by
        simpa [w] using hkBefore

      nextExponent := e
      nextOddPart := a
      nextExponent_eq := rfl

      lowerNextFactorization := hfactor

      lowerNextOdd := by
        simpa [a] using
          O.value_odd (L.index + k + 1)

      remaining_le_next := hremaining }

/-- 同期prefixを消費した後のprepared carry全データ。 -/
structure PreparedCarryData
    (O : OddOrbit) (T : TerminalPairData) where
  ordered : OrderedDifferenceData T
  lowerOrbit : TerminalLowerOrbitEmbedding O T
  boundary : SynchronizationBoundaryData O T ordered lowerOrbit
  upperFinish : ℕ
  upperRun : Runs boundary.word T.YAR upperFinish
  upperDifference :
    upperFinish = boundary.lowerFinish +
      2 ^ (ordered.depth - twoSteps boundary.word) *
        3 ^ oddSteps boundary.word * ordered.oddPart
  upperDifferenceOdd :
    Odd (3 ^ oddSteps boundary.word * ordered.oddPart)

namespace PreparedCarryData

/-- prepared carryの残り差深さ。 -/
def remainingDepth
    {O : OddOrbit} {T : TerminalPairData}
    (P : PreparedCarryData O T) : ℕ :=
  P.ordered.depth - twoSteps P.boundary.word

/-- 同期prefix消費後も残り差深さは正。 -/
theorem remainingDepth_pos
    {O : OddOrbit} {T : TerminalPairData}
    (P : PreparedCarryData O T) :
    0 < P.remainingDepth := by
  unfold remainingDepth
  exact Nat.sub_pos_of_lt P.boundary.consumed_lt

/-- 元差深さは消費総指数と残り深さへexactに分解される。 -/
theorem depth_balance
    {O : OddOrbit} {T : TerminalPairData}
    (P : PreparedCarryData O T) :
    P.ordered.depth =
      twoSteps P.boundary.word + P.remainingDepth := by
  unfold remainingDepth
  have hle :
      twoSteps P.boundary.word ≤ P.ordered.depth :=
    Nat.le_of_lt P.boundary.consumed_lt
  exact (Nat.add_sub_of_le hle).symm

/-- prepared深さは元差深さ以下。 -/
theorem remainingDepth_le_original
    {O : OddOrbit} {T : TerminalPairData}
    (P : PreparedCarryData O T) :
    P.remainingDepth ≤ P.ordered.depth := by
  unfold remainingDepth
  omega

/-- 同期語長とprepared深さの和は元差深さ以下。 -/
theorem syncLength_add_remainingDepth_le_original
    {O : OddOrbit} {T : TerminalPairData}
    (P : PreparedCarryData O T) :
    P.boundary.word.length + P.remainingDepth ≤ P.ordered.depth := by
  have hvalid := P.boundary.lowerRun.valid
  have hlen : P.boundary.word.length ≤ twoSteps P.boundary.word := by
    simpa [oddSteps] using oddSteps_le_twoSteps hvalid
  rw [P.depth_balance]
  omega

/-- ordered terminal差分と下側軌道位置からprepared carryを自動構成する。 -/
noncomputable def ofOrbit
    {O : OddOrbit}
    {T : TerminalPairData}
    (D : OrderedDifferenceData T)
    (L : TerminalLowerOrbitEmbedding O T) :
    PreparedCarryData O T := by
  let B := synchronizationBoundaryOfOrbit D L
  let upper :=
    B.lowerFinish +
      2 ^ (D.depth - twoSteps B.word) *
        3 ^ oddSteps B.word * D.oddPart
  have hrun0 :
      Runs B.word
        (T.YA + 2 ^ D.depth * D.oddPart)
        upper := by
    dsimp [upper]
    exact B.lowerRun.runs_replay_of_gap_depth_gt_twoSteps
      B.consumed_lt
  have hrun : Runs B.word T.YAR upper := by
    rw [D.difference]
    exact hrun0
  have hodd :
      Odd (3 ^ oddSteps B.word * D.oddPart) := by
    exact
      (show Odd (3 ^ oddSteps B.word) by
        exact (show Odd (3 : ℕ) by decide).pow).mul D.oddPart_odd
  exact
    { ordered := D
      lowerOrbit := L
      boundary := B
      upperFinish := upper
      upperRun := hrun
      upperDifference := rfl
      upperDifferenceOdd := hodd }

end PreparedCarryData
end CollatzSecondLayer
