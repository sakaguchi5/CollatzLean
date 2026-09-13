import CollatzLean.Collatz3.Bridge.CollatzLogPhaseRun
import CollatzLean.Collatz3.Critical.FirstPassage
import CollatzLean.Collatz3.Semantics.FirstPassage

/-!

# Collatz3 Bridge: coefficient first-passage から critical first-passage へ

`CriticalFirstPassage` は Beatty depth で書かれている。

ここでは同じ条件を、pure coefficient
`3^k / 2^E`が初めて `1` を下回るという power inequality で受け取る入口を作る。

terminal では`2^(E-1) ≤ 3^m < 2^E`を要求し、proper odd cut では
`2^(prefixDepth k) ≤ 3^k`を要求する。

critical terminal depth における strict inequality
`3^m < 2^(criticalTwoDepth m)`自体は Critical 基礎層の一般定理を再利用する。

この Bridge では、
* terminal power window から critical terminal depth を一意に復元すること、
* prefix power inequality から Beatty roof 条件を復元すること、
を証明し、既存の `CriticalFirstPassage` を derived theorem として得る。

さらに actual finite run について、
* 全 step start が始点 `x` 以上、
* endpoint も `x` 以上、
* coefficient first-passage、
だけを束ねた薄い finite suffix-minimum window を定義する。
無限軌道や将来全体は primitive data に入れない。
-/

namespace Collatz3
namespace Critical

/--
`2^(E-1) ≤ 3^m < 2^E` なら、
`E` は critical terminal depth そのもの。
-/
theorem criticalTwoDepth_eq_of_powerWindow
    {m E : ℕ}
    (hPrev : 2 ^ (E - 1) ≤ 3 ^ m)
    (hNow : 3 ^ m < 2 ^ E) :
    E = criticalTwoDepth m := by
  have hEPos : 0 < E := by
    by_contra h
    have hE0 : E = 0 := Nat.eq_zero_of_not_pos h
    subst E
    simp at hNow
  let q := E - 1
  have hEq : E = q + 1 := by
    dsimp [q]
    omega
  have hUpper : 3 ^ m ≤ 2 ^ (q + 1) := by
    rw [← hEq]
    exact Nat.le_of_lt hNow
  have hBeatLeQ : beattyIndex m ≤ q :=
    beattyIndex_le_of_upper hUpper
  have hQLeBeat : q ≤ beattyIndex m := by
    by_contra h
    have hBeatLtQ : beattyIndex m < q :=
      Nat.lt_of_not_ge h
    have hDepthLeQ : criticalTwoDepth m ≤ q := by
      unfold criticalTwoDepth
      omega
    have hPowLe :
        2 ^ criticalTwoDepth m ≤ 2 ^ q :=
      Nat.pow_le_pow_right
        (by decide : 0 < (2 : ℕ))
        hDepthLeQ
    have hPrevQ : 2 ^ q ≤ 3 ^ m := by
      simpa [q] using hPrev
    have hStrict :=
      threePow_lt_twoPow_criticalTwoDepth m
    exact
      (not_lt_of_ge (le_trans hPowLe hPrevQ))
        hStrict
  have hQ : q = beattyIndex m :=
    Nat.le_antisymm hQLeBeat hBeatLeQ
  rw [hEq, hQ]
  rfl


/--
power coefficient が expansion 側にある cut では、
prefix two-depth は Beatty roof 以下にある。

すなわち

`2^(prefixTwoDepth w k) ≤ 3^k`

から

`prefixTwoDepth w k ≤ beattyIndex k`

を復元する。
-/
theorem prefixDepth_le_beatty_of_powerCoefficient
    {w : Word}
    {k : ℕ}
    (hPow : 2 ^ Word.prefixTwoDepth w k ≤ 3 ^ k) :
    Word.prefixTwoDepth w k ≤ beattyIndex k := by
  by_contra h
  have hDepthLe :
      criticalTwoDepth k ≤ Word.prefixTwoDepth w k := by
    unfold criticalTwoDepth
    omega
  have hPowLe :
      2 ^ criticalTwoDepth k ≤
        2 ^ Word.prefixTwoDepth w k :=
    Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ))
      hDepthLe
  have hStrict :=
    threePow_lt_twoPow_criticalTwoDepth k
  exact
    (not_lt_of_ge (le_trans hPowLe hPow))
      hStrict

end Critical


namespace Word

/--
coefficient が terminal の最後の `/2` で初めて contraction 側へ入る有限 word。

terminal では

`2^(E-1) ≤ 3^m < 2^E`

を要求し、各 proper odd cut では

`2^(prefixTwoDepth w k) ≤ 3^k`

を要求する。

これは pure power inequality だけで記述した
critical first-passage の入口である。
-/
def CoefficientFirstPassage
    (w : Word) : Prop :=
  2 ^ (twoSteps w - 1) ≤ 3 ^ oddSteps w ∧
    3 ^ oddSteps w < 2 ^ twoSteps w ∧
    ∀ k : ℕ,
      k < oddSteps w →
      2 ^ prefixTwoDepth w k ≤ 3 ^ k


namespace CoefficientFirstPassage

/--
coefficient first-passage word は非空。
-/
theorem nonempty
    {w : Word}
    (h : CoefficientFirstPassage w) :
    w ≠ [] := by
  intro hw
  subst w
  simp [CoefficientFirstPassage] at h


/--
coefficient first-passage には少なくとも一つ odd step がある。
-/
theorem oddSteps_pos
    {w : Word}
    (h : CoefficientFirstPassage w) :
    0 < oddSteps w := by
  simpa [oddSteps] using
    List.length_pos_of_ne_nil h.nonempty


/--
power inequality で書いた coefficient first-passage は、
既存の Beatty 表現による `CriticalFirstPassage` を与える。
-/
theorem critical
    {w : Word}
    (h : CoefficientFirstPassage w) :
    CriticalFirstPassage w := by
  have hTerminal :
      twoSteps w =
        Critical.criticalTwoDepth (oddSteps w) :=
    Critical.criticalTwoDepth_eq_of_powerWindow
      h.1 h.2.1
  refine ⟨hTerminal, ?_⟩
  intro k hk
  exact
    Critical.prefixDepth_le_beatty_of_powerCoefficient
      (h.2.2 k hk)

end CoefficientFirstPassage

end Word


namespace Runs

/--
非空 actual run の始点は正。
-/
theorem start_pos_of_nonempty
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    0 < x := by
  cases h with
  | nil x =>
      contradiction
  | @cons e w x m z hstep htail =>
      exact hstep.start_pos

end Runs


/--
finite suffix-minimum critical window の薄い predicate。

保持する primitive data は次の4点だけ。

* `Runs w x y` :
  actual finite run
* `Runs.AllStartsAtLeast x w x` :
  区間内の各 step start は始点 `x` 以上
* `x ≤ y` :
  terminal endpoint も始点以上
* `Word.CoefficientFirstPassage w` :
  pure coefficient は terminal で初めて contraction 側へ入る

無限軌道や将来全体は primitive data に入れない。
-/
def ActualSuffixMinimumCoefficientWindow
    (w : Word)
    (x y : ℕ) : Prop :=
  Runs w x y ∧
    Runs.AllStartsAtLeast x w x ∧
    x ≤ y ∧
    Word.CoefficientFirstPassage w


namespace ActualSuffixMinimumCoefficientWindow

/--
underlying actual run。
-/
theorem run
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    Runs w x y :=
  h.1

/--
区間内の各 step start は始点以上。
-/
theorem allStartsAtLeast
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    Runs.AllStartsAtLeast x w x :=
  h.2.1

/--
endpoint も始点以上。
-/
theorem endpoint_ge
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    x ≤ y :=
  h.2.2.1

/--
pure coefficient first-passage。
-/
theorem coefficient
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    Word.CoefficientFirstPassage w :=
  h.2.2.2

/--
finite suffix-minimum coefficient window は
既存の `ActualFirstPassage` を与える。

actual run と coefficient first-passage から得られる
`CriticalFirstPassage` だけを使う derived theorem。
-/
theorem actualFirstPassage
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    ActualFirstPassage w x y :=
  ⟨h.run, h.coefficient.critical⟩


/--
finite suffix-minimum coefficient window の始点は正。
-/
theorem start_pos
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    0 < x := by
  exact
    h.run.start_pos_of_nonempty
      h.coefficient.nonempty

end ActualSuffixMinimumCoefficientWindow

end Collatz3
