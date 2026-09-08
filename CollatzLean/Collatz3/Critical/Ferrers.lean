import CollatzLean.Collatz3.Critical.Profile
import CollatzLean.Collatz3.Combinatorics.YoungFerrers
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
/-!
# Collatz3: critical Ferrers view

`Critical.Profile m` を新しい巨大 structure に包まない。
profile 自身を ordered column diagram として読む view と、
そこから導く cell 数・cut depth・critical chord rank だけを定義する。

古典 Ferrers 条件は別 predicate `IsClassicalFerrers` として切り離す。
したがって「critical profile なら自動的に Young/Ferrers partition」という
不要な仮定を基礎定義へ混ぜない。
-/

namespace Collatz3
namespace Critical

open scoped BigOperators

/-- critical profile を列順序を保った有限列図形として読む。 -/
def ferrersDiagram
    {m : ℕ}
    (h : Profile m) :
    Combinatorics.OrderedColumnDiagram m :=
  h

@[simp] theorem ferrersDiagram_height
    {m : ℕ}
    (h : Profile m)
    (k : Fin m) :
    ferrersDiagram h k = h k :=
  rfl

/-- critical Ferrers view の cell 数。 -/
def ferrersArea
    {m : ℕ}
    (h : Profile m) : ℕ :=
  Combinatorics.cellCount (ferrersDiagram h)

/-- area は profile depth の総和そのもの。 -/
theorem ferrersArea_eq_sum
    {m : ℕ}
    (h : Profile m) :
    ferrersArea h = ∑ k : Fin m, h k := by
  rfl

/--
critical profile の列高が偶然 antitone である場合にだけ成立する古典 Ferrers 条件。
-/
def IsClassicalFerrers
    {m : ℕ}
    (h : Profile m) : Prop :=
  Combinatorics.IsFerrers (ferrersDiagram h)

/-- 古典 Ferrers 条件を持つ critical profile を classical shape に上げる。 -/
def toClassicalFerrers
    {m : ℕ}
    (h : Profile m)
    (hFerrers : IsClassicalFerrers h) :
    Combinatorics.FerrersShape m :=
  ⟨ferrersDiagram h, hFerrers⟩

/--
profile が表す cut depth。
proper cut `k < m` では profile checkpoint、terminal 以後では critical terminal depth を使う。
この saturation により rank 関数を `ℕ → ℤ` として薄く扱える。
-/
def cutDepth
    {m : ℕ}
    (h : Profile m)
    (k : ℕ) : ℕ :=
  if hk : k < m then
    checkpoint h ⟨k, hk⟩
  else
    criticalTwoDepth m

@[simp] theorem cutDepth_of_lt
    {m : ℕ}
    (h : Profile m)
    {k : ℕ}
    (hk : k < m) :
    cutDepth h k = checkpoint h ⟨k, hk⟩ := by
  simp [cutDepth, hk]

@[simp] theorem cutDepth_of_le
    {m : ℕ}
    (h : Profile m)
    {k : ℕ}
    (hk : m ≤ k) :
    cutDepth h k = criticalTwoDepth m := by
  simp [cutDepth, Nat.not_lt.mpr hk]

@[simp] theorem cutDepth_terminal
    {m : ℕ}
    (h : Profile m) :
    cutDepth h m = criticalTwoDepth m := by
  exact cutDepth_of_le h (Nat.le_refl m)

/--
critical profile から導く chord rank。
terminal total depth `H = criticalTwoDepth m` を固定し、
`H*k - m*cutDepth(k)` を整数値で持つ。
-/
def profileChordRank
    {m : ℕ}
    (h : Profile m)
    (k : ℕ) : ℤ :=
  (criticalTwoDepth m : ℤ) * (k : ℤ) -
    (m : ℤ) * (cutDepth h k : ℤ)

/-- terminal rank は常に 0。 -/
@[simp] theorem profileChordRank_terminal_eq_zero
    {m : ℕ}
    (h : Profile m) :
    profileChordRank h m = 0 := by
  unfold profileChordRank
  rw [cutDepth_terminal]
  ring

/-- admissible nonempty profile の initial rank も 0。 -/
@[simp] theorem profileChordRank_zero_eq_zero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    profileChordRank h 0 = 0 := by
  unfold profileChordRank
  rw [cutDepth_of_lt h hm]
  rw [A.first_checkpoint_eq_zero hm]
  simp

end Critical
end Collatz3
