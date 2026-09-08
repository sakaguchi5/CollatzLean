import CollatzLean.Collatz3.Semantics.ReachOne
import CollatzLean.Collatz3.Semantics.PeriodicOrbit
import CollatzLean.Collatz3.Semantics.OddOrbit

/-!
# Collatz3: 無限 odd-only 軌道の最終挙動

このファイルでは、無限軌道の最終挙動を表すための薄い述語だけを置く。

* `HitsOne` : ある時刻で値 `1` に到達する。
* `HasNontrivialRepeat` : `1` 以外の値を二度通る。
* `DivergesToInfinity` : 任意の有限境界を、ある時刻以降ずっと上回る。

`HasNontrivialRepeat` は非自明周期の場合の最も薄い有限証明書である。
odd-only step の決定性により、同じ整数への再訪は実際の return segment を与える。
primitive return への正規化はここには埋め込まない。

3述語の「どれかが必ず成立する」という無限三分法は古典的選択を必要とするため、
`OrbitFateClassical` に隔離する。このファイル自身はその完全性を仮定しない。
-/

namespace Collatz3
namespace OddOrbit

/-- 無限 odd-only 軌道が有限時刻で `1` に到達する。 -/
def HitsOne (O : OddOrbit) : Prop :=
  ∃ n : ℕ, O.value n = 1

/--
無限 odd-only 軌道が `1` 以外の同じ値を二度通る。
これは非自明周期へ入ったことの有限な repeated-state 証明書である。
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
  have hqPos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hwNonempty : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps i (j - i)
    change Word.oddSteps w = j - i at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hRun : Runs w (O.value i) (O.value i) := by
    have hSeg := O.runsSegment i (j - i)
    have hIndex : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
    change Runs w (O.value i) (O.value (i + (j - i))) at hSeg
    rw [hIndex, ← heq] at hSeg
    exact hSeg
  exact ⟨i, w, hReach, ⟨hwNonempty, hRun⟩, hiOne⟩

/-- `+∞` への発散は特に値が上に有界ではない。 -/
theorem unbounded_of_divergesToInfinity
    (O : OddOrbit)
    (h : O.DivergesToInfinity) :
    ∀ K : ℕ, ∃ n : ℕ, K < O.value n := by
  intro K
  rcases h K with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

end OddOrbit
end Collatz3
