import CollatzLean.Collatz3.Semantics.OrbitFate
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Max

/-!
# Collatz3: 無限軌道三分法の classical closure

基礎語彙と有限深度三分法は `OrbitFate` / `FiniteOrbitFate` に置き、
このファイルだけで無限軌道の完全三分法を閉じる。

`HitsOne` も非自明な再訪もないなら、軌道値列は単射である。
単射な自然数列では各有限集合の逆像も有限なので、各境界以下を訪れる時刻には最後がある。
したがって軌道は `+∞` へ発散する。

有限集合の全逆像を一つの `Finset` として選ぶ箇所が noncomputable なので、
この無限 closure のみ classical に隔離する。stable root からは import しない。
-/

namespace Collatz3
namespace OddOrbit

/-- `1` に到達せず非自明な再訪もない軌道では、時刻から値への写像は単射。 -/
theorem value_injective_of_no_hit_no_repeat
    (O : OddOrbit)
    (hHit : ¬ O.HitsOne)
    (hRepeat : ¬ O.HasNontrivialRepeat) :
    Function.Injective O.value := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hiOne : O.value i ≠ 1 := by
      intro hi
      exact hHit ⟨i, hi⟩
    exact hRepeat ⟨i, j, hlt, hij, hiOne⟩
  · have hjOne : O.value j ≠ 1 := by
      intro hj
      exact hHit ⟨j, hj⟩
    exact hRepeat ⟨j, i, hgt, hij.symm, hjOne⟩

/-- 単射な自然数値列は `+∞` へ発散する。 -/
theorem divergesToInfinity_of_value_injective
    (O : OddOrbit)
    (hInjective : Function.Injective O.value) :
    O.DivergesToInfinity := by
  intro K
  let low : Finset ℕ := Finset.range (K + 1)
  have hInjOn :
      Set.InjOn O.value (O.value ⁻¹' (↑low : Set ℕ)) := by
    intro a ha b hb hab
    exact hInjective hab
  let pre : Finset ℕ := low.preimage O.value hInjOn
  by_cases hPre : pre.Nonempty
  · obtain ⟨m, hm, hMax⟩ :=
      Finset.exists_max_image pre (fun n : ℕ => n) hPre
    refine ⟨m + 1, ?_⟩
    intro n hn
    by_contra hNot
    have hLe : O.value n ≤ K := Nat.le_of_not_gt hNot
    have hLt : O.value n < K + 1 := by omega
    have hLow : O.value n ∈ low := by
      simpa [low] using hLt
    have hnPre : n ∈ pre := by
      simpa [pre] using hLow
    have hnm : n ≤ m := by
      simpa using hMax n hnPre
    omega
  · refine ⟨0, ?_⟩
    intro n hn
    by_contra hNot
    have hLe : O.value n ≤ K := Nat.le_of_not_gt hNot
    have hLt : O.value n < K + 1 := by omega
    have hLow : O.value n ∈ low := by
      simpa [low] using hLt
    have hnPre : n ∈ pre := by
      simpa [pre] using hLow
    exact hPre ⟨n, hnPre⟩

/-- `1` に到達せず非自明な再訪もないなら、残る可能性は `+∞` への発散。 -/
theorem divergesToInfinity_of_no_hit_no_repeat
    (O : OddOrbit)
    (hHit : ¬ O.HitsOne)
    (hRepeat : ¬ O.HasNontrivialRepeat) :
    O.DivergesToInfinity :=
  divergesToInfinity_of_value_injective O
    (value_injective_of_no_hit_no_repeat O hHit hRepeat)

/--
無限 odd-only 軌道の完全三分法。

1. 有限時間で `1` に到達する。
2. `1` 以外の同じ値を二度通り、非自明周期の有限証明書を持つ。
3. `+∞` へ発散する。

完全性のための古典的場合分けはこの theorem とこのファイルだけに隔離する。
-/
theorem fate_trichotomy
    (O : OddOrbit) :
    O.HitsOne ∨
      O.HasNontrivialRepeat ∨
      O.DivergesToInfinity := by
  by_cases hHit : O.HitsOne
  · exact Or.inl hHit
  · by_cases hRepeat : O.HasNontrivialRepeat
    · exact Or.inr (Or.inl hRepeat)
    · exact Or.inr (Or.inr (divergesToInfinity_of_no_hit_no_repeat O hHit hRepeat))

end OddOrbit
end Collatz3
