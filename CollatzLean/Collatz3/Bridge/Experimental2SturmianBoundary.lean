import CollatzLean.Collatz3.Bridge.Experimental2BeattyInverse
import CollatzLean.Collatz3.Critical.FirstPassage

/-!
# Collatz3 Bridge: mechanical inverse から Sturmian boundary / first-passage へ

`Experimental2BeattyInverse` では、Beatty roof

`beattyIndex(m) = floor(m * log₂ 3)`

の離散逆

`beattyInverseHeight(k) = min {m | k ≤ beattyIndex m}`

を構成し、正の `k` では power-form の最小境界

`min {m | 2^k < 3^m}`

と exact に一致することを証明した。

このファイルでは新しい critical-height 定義を導入しない。
代わりに、その離散逆を旧 `SturmianHeight` が担っていた利用側へ接続する。

主な内容は次の三点である。

1. `beattyInverseHeight` と `beattyIndex` が threshold について exact な Galois 型対応を持つ。
2. `beattyInverseHeight 0 = 0` なので、旧 `criticalPrefixHeight` の 0 正規化は
   新しい関数を定義せず自動的に得られる。
3. 現在の odd-only `CriticalFirstPassage` の roof 条件

   `prefixTwoDepth w k ≤ beattyIndex k`

   は、転置した Sturmian boundary 条件

   `beattyInverseHeight (prefixTwoDepth w k) ≤ k`

   と exact に同値である。

旧 parity-word 表現では横軸が全 step 数、縦軸が odd count だった。
現在の exponent-word 表現では odd cut `k` と累積 two-depth を使うため、
上の式が旧

`criticalHeight(t) ≤ prefixOddCount(t)`

の自然な転置版になる。
-/

namespace Collatz3
namespace Bridge

/--
`beattyIndex` は index に対して単調。

新しい monotonicity datum は保存せず、power-form upper inequality の最小性から導く。
-/
theorem beattyIndex_mono_via_upper
    {a b : ℕ}
    (hab : a ≤ b) :
    Critical.beattyIndex a ≤ Critical.beattyIndex b := by
  apply Critical.beattyIndex_le_of_upper
  exact le_trans
    (Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hab)
    (Critical.beattyIndex_upper b)

/--
Beatty roof とその離散逆の exact threshold 対応。

`H(k)` を `k ≤ beattyIndex(m)` を初めて満たす `m` とすると、

`H(k) ≤ m ↔ k ≤ beattyIndex(m)`。

これは inverse を単なる closed formula ではなく、roof の順序論的逆として使うための中心補題。
-/
theorem beattyInverseHeight_le_iff_le_beattyIndex
    {k m : ℕ} :
    beattyInverseHeight k ≤ m ↔
      k ≤ Critical.beattyIndex m := by
  constructor
  · intro hInv
    have hSpec :
        k ≤ Critical.beattyIndex (beattyInverseHeight k) :=
      beattyInverseHeight_spec k
    exact le_trans hSpec (beattyIndex_mono_via_upper hInv)
  · intro hReach
    exact beattyInverseHeight_le_of_reaches hReach

/-- threshold 対応を roof 側から読む対称形。 -/
theorem le_beattyIndex_iff_beattyInverseHeight_le
    {k m : ℕ} :
    k ≤ Critical.beattyIndex m ↔
      beattyInverseHeight k ≤ m := by
  exact beattyInverseHeight_le_iff_le_beattyIndex.symm

/--
Beatty 離散逆は時刻 `0` を既に `0` に正規化している。

旧 power-form critical height は `k=0` で `1` だったため
`criticalPrefixHeight 0 := 0` という別定義が必要だったが、
mechanical inverse ではその補正は definition の外側で不要になる。
-/
@[simp] theorem beattyInverseHeight_zero :
    beattyInverseHeight 0 = 0 := by
  simp only [beattyInverseHeight, Experimental2.IsLowerMechanicalRoof.inverse_zero]

/--
正の power-form Sturmian boundary は exact に `ceil(k * log₃ 2)`。

左辺 `IsPowerCriticalHeight k m` は

* `2^k < 3^m`、
* それより小さい height ではまだ成立しない、

だけを持つ薄い boundary specification である。
-/
theorem isPowerCriticalHeight_iff_eq_natCeil_mul_logb_three_two
    {k m : ℕ}
    (hk : 0 < k) :
    IsPowerCriticalHeight k m ↔
      m = ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  rw [isPowerCriticalHeight_iff_eq_beattyInverseHeight hk]
  rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/--
旧 `criticalPrefixHeight` 型の「0 だけ正規化した power boundary」は一意であり、
その正本は `beattyInverseHeight` である。

したがって新しい normalized critical-height function を別定義する必要はない。
-/
theorem normalizedPowerCriticalHeight_iff_eq_beattyInverseHeight
    {H : ℕ → ℕ} :
    (H 0 = 0 ∧
      ∀ k : ℕ, 0 < k → IsPowerCriticalHeight k (H k)) ↔
      H = beattyInverseHeight := by
  constructor
  · rintro ⟨hZero, hPos⟩
    funext k
    by_cases hkZero : k = 0
    · subst k
      rw [hZero, beattyInverseHeight_zero]
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
      exact
        (isPowerCriticalHeight_iff_eq_beattyInverseHeight hkPos).1
          (hPos k hkPos)
  · intro hEq
    subst H
    constructor
    · exact beattyInverseHeight_zero
    · intro k hk
      exact beattyInverseHeight_isPowerCriticalHeight hk

/--
任意の exponent word の odd cut `k` で、
Beatty roof 以下にいることと inverse Sturmian boundary 以上にいることは exact に同値。

これは roof 座標と転置 boundary 座標を行き来する基本変換。
-/
theorem prefixTwoDepth_le_beatty_iff_inverseBoundary
    (w : Word)
    (k : ℕ) :
    Word.prefixTwoDepth w k ≤ Critical.beattyIndex k ↔
      beattyInverseHeight (Word.prefixTwoDepth w k) ≤ k := by
  exact
    le_beattyIndex_iff_beattyInverseHeight_le
      (k := Word.prefixTwoDepth w k)
      (m := k)

/--
同じ boundary 条件を `log₃ 2` の ceiling で直接表示する。

`beattyInverseHeight` を消しても内容は同じである。
-/
theorem prefixTwoDepth_le_beatty_iff_natCeil_logb_three_two_le
    (w : Word)
    (k : ℕ) :
    Word.prefixTwoDepth w k ≤ Critical.beattyIndex k ↔
      ⌈(Word.prefixTwoDepth w k : ℝ) * Real.logb 3 2⌉₊ ≤ k := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/--
critical first-passage word の各 proper odd cut は、
転置した Sturmian boundary の上側にある。

旧 parity-word theorem

`criticalHeight(t) ≤ prefixOddCount(t)`

を現在の odd-only exponent-word 座標へ移した形。
-/
theorem criticalFirstPassage_prefix_above_inverseBoundary
    {w : Word}
    (P : Word.CriticalFirstPassage w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    beattyInverseHeight (Word.prefixTwoDepth w k) ≤ k := by
  exact
    (prefixTwoDepth_le_beatty_iff_inverseBoundary w k).1
      (P.prefixDepth_le_beatty hk)

/--
前定理の解析的表示。

各 proper odd cut `k` で

`ceil(prefixTwoDepth * log₃ 2) ≤ k`。
-/
theorem criticalFirstPassage_prefix_above_sturmianCeil
    {w : Word}
    (P : Word.CriticalFirstPassage w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    ⌈(Word.prefixTwoDepth w k : ℝ) * Real.logb 3 2⌉₊ ≤ k := by
  exact
    (prefixTwoDepth_le_beatty_iff_natCeil_logb_three_two_le w k).1
      (P.prefixDepth_le_beatty hk)

/--
`CriticalFirstPassage` 全体を inverse-boundary 座標で exact に特徴付ける。

terminal 条件はそのまま保持し、proper-prefix の Beatty roof 条件だけを

`beattyInverseHeight(prefixTwoDepth) ≤ oddCut`

へ置き換える。

したがって first-passage の「屋根より下」という記述と
Sturmian inverse boundary の「境界より上」という記述は同じ admissible class を表す。
-/
theorem criticalFirstPassage_iff_terminal_and_inverseBoundary
    (w : Word) :
    Word.CriticalFirstPassage w ↔
      Word.twoSteps w = Critical.criticalTwoDepth (Word.oddSteps w) ∧
        ∀ k : ℕ,
          k < Word.oddSteps w →
          beattyInverseHeight (Word.prefixTwoDepth w k) ≤ k := by
  constructor
  · intro P
    constructor
    · exact P.totalTwoDepth_eq
    · intro k hk
      exact criticalFirstPassage_prefix_above_inverseBoundary P hk
  · rintro ⟨hTerminal, hBoundary⟩
    constructor
    · exact hTerminal
    · intro k hk
      exact
        (prefixTwoDepth_le_beatty_iff_inverseBoundary w k).2
          (hBoundary k hk)

/--
`CriticalFirstPassage` の完全な `log₃ 2`-Sturmian 表示。

新しい slope data や critical-height definition を導入せず、
既存の terminal equation と ceiling boundary だけで first-passage を記述する。
-/
theorem criticalFirstPassage_iff_terminal_and_sturmianCeil
    (w : Word) :
    Word.CriticalFirstPassage w ↔
      Word.twoSteps w = Critical.criticalTwoDepth (Word.oddSteps w) ∧
        ∀ k : ℕ,
          k < Word.oddSteps w →
          ⌈(Word.prefixTwoDepth w k : ℝ) * Real.logb 3 2⌉₊ ≤ k := by
  constructor
  · intro P
    constructor
    · exact P.totalTwoDepth_eq
    · intro k hk
      exact criticalFirstPassage_prefix_above_sturmianCeil P hk
  · rintro ⟨hTerminal, hBoundary⟩
    apply (criticalFirstPassage_iff_terminal_and_inverseBoundary w).2
    refine ⟨hTerminal, ?_⟩
    intro k hk
    have hCeil := hBoundary k hk
    rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]
    exact hCeil

end Bridge
end Collatz3
