import CollatzLean.Collatz3.Experimental2.RoofPath
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: 一般屋根の弦順位

`Experimental2` の一般整数値屋根 `β : ℕ → ℕ` と有限経路 `height : ℕ → ℕ` に対して、
RecordFerrers 型の record 幾何で使う最小限の弦順位だけを定義する。

このファイルでは

* `Critical.beattyIndex`,
* `Critical.Profile`,
* `Ferrers.RecordFerrers`,
* 実際の Collatz 軌道

には依存しない。

終端幅を `m` とすると、終端深さは既存の一般定義

`criticalDepth β m = β m + 1`

を使う。proper cut では `height k`、終端以後では `criticalDepth β m` に飽和させた
`cutDepth` を置き、終端弦からの整数値順位

`chordRank(k) = criticalDepth β m * k - m * cutDepth(k)`

を定義する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
一般屋根経路の cut depth。

`k < m` では経路の高さ `height k` を使い、`m ≤ k` では終端深さ
`criticalDepth β m` に飽和させる。
-/
def cutDepth
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (k : ℕ) : ℕ :=
  if _hk : k < m then
    height k
  else
    criticalDepth β m

@[simp] theorem cutDepth_of_lt
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {k : ℕ}
    (hk : k < m) :
    cutDepth β m height k = height k := by
  simp [cutDepth, hk]

@[simp] theorem cutDepth_of_le
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {k : ℕ}
    (hk : m ≤ k) :
    cutDepth β m height k = criticalDepth β m := by
  simp [cutDepth, Nat.not_lt.mpr hk]

@[simp] theorem cutDepth_terminal
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) :
    cutDepth β m height m = criticalDepth β m := by
  exact cutDepth_of_le (β := β) (height := height) (Nat.le_refl m)

/--
一般屋根経路の弦順位。

終端点 `(m, criticalDepth β m)` と原点を結ぶ弦に対して、
cut `k` の高さがどちら側にあるかを整数演算だけで測る。
-/
def chordRank
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (k : ℕ) : ℤ :=
  (criticalDepth β m : ℤ) * (k : ℤ) -
    (m : ℤ) * (cutDepth β m height k : ℤ)

/-- proper cut では弦順位は実際の `height k` で読める。 -/
theorem chordRank_of_lt
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {k : ℕ}
    (hk : k < m) :
    chordRank β m height k =
      (criticalDepth β m : ℤ) * (k : ℤ) -
        (m : ℤ) * (height k : ℤ) := by
  unfold chordRank
  rw [cutDepth_of_lt (β := β) (height := height) hk]

/-- 終端点は定義上、終端弦そのものに乗るので順位は `0`。 -/
@[simp] theorem chordRank_terminal_eq_zero
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) :
    chordRank β m height m = 0 := by
  unfold chordRank
  rw [cutDepth_terminal]
  ring

/--
原点の高さが `0` なら原点の弦順位も `0`。
後段で admissible path から原点条件を回収するときに使う薄い補題。
-/
@[simp] theorem chordRank_zero_eq_zero_of_height_zero
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (hm : 0 < m)
    (h0 : height 0 = 0) :
    chordRank β m height 0 = 0 := by
  rw [chordRank_of_lt (β := β) (height := height) hm]
  simp [h0]

end GenericRecordFerrers
end Experimental2
end Collatz3
