import CollatzLean.Collatz3.Semantics.ReachOne
import CollatzLean.Collatz3.Semantics.PeriodicOrbit
import CollatzLean.Collatz3.Semantics.OddOrbit


/-!
# Collatz3: 無限 odd-only 軌道の最終挙動

このファイルでは、無限軌道の最終挙動を表すための薄い述語だけを正本に置く。

* `HitsOne` : ある時刻で値 `1` に到達する。
* `HasNontrivialRepeat` : `1` 以外の値を二度通る。
* `DivergesToInfinity` : 任意の有限境界を、ある時刻以降ずっと上回る。

正規有限証明書は derived theorem として取り出す。

* `HitsOne` は開始値の `ReachesOne` と同値で、開始値が `1` でなければ唯一の `FirstHitsOne` word を持つ。
* `HasNontrivialRepeat` からは到達可能な非自明 `PrimitiveReturn` を取り出せる。
* 三つの意味論的枝が互いに排他的であることは、この stable / constructive 層で証明する。

3述語の「どれかが必ず成立する」という無限三分法の網羅性だけは
`OrbitFateClassical` に隔離する。
-/

namespace Collatz3
namespace OddOrbit

/-- 無限 odd-only 軌道が有限時刻で `1` に到達する。 -/
def HitsOne (O : OddOrbit) : Prop :=
  ∃ n : ℕ, O.value n = 1

/--
無限 odd-only 軌道が `1` 以外の同じ値を二度通る。
これは非自明周期へ入ったことの最も薄い repeated-state 証明書である。
-/
def HasNontrivialRepeat (O : OddOrbit) : Prop :=
  ∃ i j : ℕ,
    i < j ∧
    O.value i = O.value j ∧
    O.value i ≠ 1

/--
無限 odd-only 軌道が `+∞` へ発散する。
任意の境界 `K` に対して、ある時刻以降は常に `K` より大きい。
-/
def DivergesToInfinity (O : OddOrbit) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < O.value n

/-- 軌道上で `1` を実際に通れば、開始値も有限時間後に `1` へ到達する。 -/
theorem reachesOne_of_hitsOne
    (O : OddOrbit)
    (h : O.HitsOne) :
    ReachesOne (O.value 0) := by
  rcases h with ⟨n, hn⟩
  change Reaches (O.value 0) 1
  refine ⟨O.segmentWord 0 n, ?_⟩
  have hRun := O.runsSegment 0 n
  simpa [hn] using hRun

/--
開始値から有限 run で `1` へ到達できるなら、実際の無限軌道も同じ step 数で `1` を通る。
finite run の同長決定性を使う。
-/
theorem hitsOne_of_reachesOne
    (O : OddOrbit)
    (h : ReachesOne (O.value 0)) :
    O.HitsOne := by
  rcases h.exists_endsAtOne with ⟨w, hw⟩
  have hOrbit := O.runsSegment 0 (Word.oddSteps w)
  have hDet :=
    Runs.word_end_eq_of_common_start_same_oddSteps
      hw hOrbit (by simp)
  refine ⟨Word.oddSteps w, ?_⟩
  simpa using hDet.2.symm

/-- `HitsOne` と開始値の `ReachesOne` は exact に同じ第1分類を表す。 -/
theorem hitsOne_iff_reachesOne
    (O : OddOrbit) :
    O.HitsOne ↔ ReachesOne (O.value 0) := by
  constructor
  · exact O.reachesOne_of_hitsOne
  · exact O.hitsOne_of_reachesOne

/--
非自明な再訪は、開始点から到達できる `1` 以外の整数上に
実際の非空 return segment を与える。
-/
theorem exists_nontrivial_return_of_repeat
    (O : OddOrbit)
    (h : O.HasNontrivialRepeat) :
    ∃ i : ℕ, ∃ w : Word,
      Reaches (O.value 0) (O.value i) ∧
      ReturnsTo w (O.value i) ∧
      O.value i ≠ 1 := by
  rcases h with ⟨i, j, hij, heq, hiOne⟩
  let w : Word := O.segmentWord i (j - i)
  have hReach : Reaches (O.value 0) (O.value i) := by
    refine ⟨O.segmentWord 0 i, ?_⟩
    simpa using O.runsSegment 0 i
  have hwNonempty : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps i (j - i)
    change Word.oddSteps w = j - i at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hRun : Runs w (O.value i) (O.value i) := by
    have hSeg := O.runsSegment i (j - i)
    have hIndex : i + (j - i) = j :=
      Nat.add_sub_of_le (Nat.le_of_lt hij)
    change Runs w (O.value i) (O.value (i + (j - i))) at hSeg
    rw [hIndex, ← heq] at hSeg
    exact hSeg
  exact ⟨i, w, hReach, ⟨hwNonempty, hRun⟩, hiOne⟩

/--
非自明な再訪を、到達可能な基点上の primitive return へ正規化する。
-/
theorem exists_nontrivial_primitiveReturn_of_repeat
    (O : OddOrbit)
    (h : O.HasNontrivialRepeat) :
    ∃ i : ℕ, ∃ w : Word,
      Reaches (O.value 0) (O.value i) ∧
      PrimitiveReturn w (O.value i) ∧
      O.value i ≠ 1 := by
  rcases O.exists_nontrivial_return_of_repeat h with
    ⟨i, w, hReach, hReturn, hiOne⟩
  rcases ReturnsTo.exists_primitiveReturn hReturn with ⟨v, hv⟩
  exact ⟨i, v, hReach, hv, hiOne⟩

/--
第2分類の正規化。
非自明な再訪から、開始値から到達可能な基点上の primitive nontrivial periodic orbit を得る。
-/
theorem exists_eventual_nontrivialPeriodicOrbit_of_repeat
    (O : OddOrbit)
    (h : O.HasNontrivialRepeat) :
    ∃ i : ℕ, ∃ w : Word,
      Reaches (O.value 0) (O.value i) ∧
      IsNontrivialPeriodicOrbit w (O.value i) := by
  rcases O.exists_nontrivial_primitiveReturn_of_repeat h with
    ⟨i, w, hReach, hPrimitive, hiOne⟩
  exact ⟨i, w, hReach, ⟨hPrimitive, hiOne⟩⟩

/-- `+∞` への発散は特に値が上に有界ではない。 -/
theorem unbounded_of_divergesToInfinity
    (O : OddOrbit)
    (h : O.DivergesToInfinity) :
    ∀ K : ℕ, ∃ n : ℕ, K < O.value n := by
  intro K
  rcases h K with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

/-- 第1分類と第2分類は同時には起こらない。 -/
theorem hitsOne_disjoint_nontrivialRepeat
    (O : OddOrbit)
    (hHit : O.HitsOne)
    (hRepeat : O.HasNontrivialRepeat) :
    False := by
  rcases hHit with ⟨n, hn⟩
  rcases hRepeat with ⟨i, j, hij, heq, hiOne⟩
  let d : ℕ := j - i
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hij
  have hOccurrences :=
    O.value_eq_repeat_base_mul_period hij heq
  let k : ℕ := n + 1
  let t : ℕ := i + k * d
  have hMul : k ≤ k * d := by
    have hOneLe : 1 ≤ d := Nat.succ_le_of_lt hd
    have h := Nat.mul_le_mul_left k hOneLe
    simpa using h
  have hnk : n ≤ k := by
    dsimp [k]
    omega
  have hnMul : n ≤ k * d :=
    le_trans hnk hMul
  have hnt : n ≤ t := by
    dsimp [t]
    exact le_trans hnMul (Nat.le_add_left (k * d) i)
  have htOne : O.value t = 1 :=
    O.value_eq_one_of_hit_of_le hn hnt
  have htBase : O.value t = O.value i := by
    simpa [t, k, d] using hOccurrences k
  exact hiOne (htBase.symm.trans htOne)

/-- 第1分類と `+∞` 発散は同時には起こらない。 -/
theorem hitsOne_disjoint_divergesToInfinity
    (O : OddOrbit)
    (hHit : O.HitsOne)
    (hDiv : O.DivergesToInfinity) :
    False := by
  rcases hHit with ⟨n, hn⟩
  rcases hDiv 1 with ⟨N, hN⟩
  let t : ℕ := max n N
  have hnt : n ≤ t := by
    exact Nat.le_max_left _ _
  have hNt : N ≤ t := by
    exact Nat.le_max_right _ _
  have htOne : O.value t = 1 :=
    O.value_eq_one_of_hit_of_le hn hnt
  have hAbove : 1 < O.value t := hN t hNt
  rw [htOne] at hAbove
  omega

/-- 第2分類と `+∞` 発散は同時には起こらない。 -/
theorem nontrivialRepeat_disjoint_divergesToInfinity
    (O : OddOrbit)
    (hRepeat : O.HasNontrivialRepeat)
    (hDiv : O.DivergesToInfinity) :
    False := by
  rcases hRepeat with ⟨i, j, hij, heq, hiOne⟩
  let d : ℕ := j - i
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hij
  have hOccurrences :=
    O.value_eq_repeat_base_mul_period hij heq
  rcases hDiv (O.value i) with ⟨N, hN⟩
  let k : ℕ := N + 1
  let t : ℕ := i + k * d
  have hMul : k ≤ k * d := by
    have hOneLe : 1 ≤ d := Nat.succ_le_of_lt hd
    have h := Nat.mul_le_mul_left k hOneLe
    simpa using h
  have hNk : N ≤ k := by
    dsimp [k]
    omega
  have hNMul : N ≤ k * d :=
    le_trans hNk hMul
  have hNt : N ≤ t := by
    dsimp [t]
    exact le_trans hNMul (Nat.le_add_left (k * d) i)
  have htBase : O.value t = O.value i := by
    simpa [t, k, d] using hOccurrences k
  have hAbove : O.value i < O.value t := hN t hNt
  rw [htBase] at hAbove
  omega

/-- 三つの終局型は pairwise disjoint。網羅性とは独立に stable 層で成立する。 -/
theorem fate_pairwise_disjoint
    (O : OddOrbit) :
    (O.HitsOne → O.HasNontrivialRepeat → False) ∧
    (O.HitsOne → O.DivergesToInfinity → False) ∧
    (O.HasNontrivialRepeat → O.DivergesToInfinity → False) := by
  exact
    ⟨O.hitsOne_disjoint_nontrivialRepeat,
      ⟨O.hitsOne_disjoint_divergesToInfinity,
        O.nontrivialRepeat_disjoint_divergesToInfinity⟩⟩

end OddOrbit
end Collatz3
