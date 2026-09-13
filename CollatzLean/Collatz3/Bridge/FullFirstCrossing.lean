import CollatzLean.Collatz3.Bridge.FullCriticalRestrictedPartition

/-!
# Collatz3 Bridge: terminal overshoot を許した full first crossing

既存の `CriticalFirstPassage` / `CriticalWord m` は terminal two-depth を

`criticalTwoDepth m = beattyIndex m + 1`

に exact に固定している。

actual odd-only step では最後の 2 除算指数が大きく、critical boundary を
一度に 2 段以上飛び越えることがある。本ファイルでは proper prefix 条件を
そのまま保ち、terminal だけ

`criticalTwoDepth m ≤ twoSteps w`

へ緩めた full first-crossing 語彙を導入する。

設計は thin definitions + derived theorems とし、overshoot は
`terminalExtraDepth` という一個の自然数として後から読む。
-/

namespace Collatz3

namespace Word

/--
terminal overshoot を許した pure first-crossing 条件。

proper cut はすべて Beatty roof 以下に残り、terminal では
minimal critical depth 以上へ到達する。
-/
def FullFirstCrossing (w : Word) : Prop :=
  Critical.criticalTwoDepth (oddSteps w) ≤ twoSteps w ∧
    ∀ k : ℕ, k < oddSteps w →
      prefixTwoDepth w k ≤ Critical.beattyIndex k

namespace FullFirstCrossing

/-- terminal depth は minimal critical depth 以上。 -/
theorem terminal_le
    {w : Word}
    (h : FullFirstCrossing w) :
    Critical.criticalTwoDepth (oddSteps w) ≤ twoSteps w :=
  h.1

/-- proper prefix は従来と同じ critical roof 以下。 -/
theorem prefixDepth_le_beatty
    {w : Word}
    (h : FullFirstCrossing w)
    {k : ℕ}
    (hk : k < oddSteps w) :
    prefixTwoDepth w k ≤ Critical.beattyIndex k :=
  h.2 k hk

/-- full first-crossing word は空でない。 -/
theorem nonempty
    {w : Word}
    (h : FullFirstCrossing w) :
    w ≠ [] := by
  intro hw
  subst w
  have hDepth := h.terminal_le
  simp [Critical.criticalTwoDepth] at hDepth

/-- full first-crossing には少なくとも一つ odd step がある。 -/
theorem oddSteps_pos
    {w : Word}
    (h : FullFirstCrossing w) :
    0 < oddSteps w := by
  simpa [oddSteps] using List.length_pos_of_ne_nil h.nonempty

end FullFirstCrossing
end Word

namespace Critical

/--
幅 `m` を固定した full first-crossing word 条件。

* exponent はすべて正、
* odd-step 数は exact に `m`、
* terminal は minimal critical depth 以上、
* proper prefix は Beatty roof 以下。
-/
def IsFullFirstCrossingWord
    (m : ℕ)
    (w : Word) : Prop :=
  Word.Valid w ∧
    Word.oddSteps w = m ∧
    Word.FullFirstCrossing w

/-- 幅 `m` の terminal overshoot 込み first-crossing shape。 -/
abbrev FullFirstCrossingWord (m : ℕ) :=
  {w : Word // IsFullFirstCrossingWord m w}

namespace IsFullFirstCrossingWord

/-- full first-crossing word は valid。 -/
theorem valid
    {m : ℕ} {w : Word}
    (C : IsFullFirstCrossingWord m w) :
    Word.Valid w :=
  C.1

/-- odd-step 数は指定幅に一致。 -/
theorem oddSteps_eq
    {m : ℕ} {w : Word}
    (C : IsFullFirstCrossingWord m w) :
    Word.oddSteps w = m :=
  C.2.1

/-- terminal total depth は minimal critical depth 以上。 -/
theorem criticalTwoDepth_le_twoSteps
    {m : ℕ} {w : Word}
    (C : IsFullFirstCrossingWord m w) :
    criticalTwoDepth m ≤ Word.twoSteps w := by
  have h := C.2.2.terminal_le
  rw [C.oddSteps_eq] at h
  exact h

/-- proper prefix は critical roof 以下。 -/
theorem prefixTwoDepth_le_beatty
    {m : ℕ} {w : Word}
    (C : IsFullFirstCrossingWord m w)
    {k : ℕ}
    (hk : k < m) :
    Word.prefixTwoDepth w k ≤ beattyIndex k := by
  apply C.2.2.prefixDepth_le_beatty
  rw [C.oddSteps_eq]
  exact hk

end IsFullFirstCrossingWord

namespace FullFirstCrossingWord

/-- terminal が minimal critical depth を何段余分に越えたか。 -/
def terminalExtraDepth
    {m : ℕ}
    (W : FullFirstCrossingWord m) : ℕ :=
  Word.twoSteps W.1 - criticalTwoDepth m

/-- total two-depth は minimal depth + terminal overshoot に exact 分解される。 -/
theorem twoSteps_eq_criticalTwoDepth_add_terminalExtraDepth
    {m : ℕ}
    (W : FullFirstCrossingWord m) :
    Word.twoSteps W.1 =
      criticalTwoDepth m + terminalExtraDepth W := by
  have hLe := W.2.criticalTwoDepth_le_twoSteps
  unfold terminalExtraDepth
  omega

/-- positive width の full first-crossing word は非空。 -/
theorem nonempty
    {m : ℕ}
    (hm : 0 < m)
    (W : FullFirstCrossingWord m) :
    W.1 ≠ [] := by
  intro hNil
  have hSteps := W.2.oddSteps_eq
  rw [hNil] at hSteps
  simp [Word.oddSteps] at hSteps
  omega

/-- overshoot が `0` なら従来の exact critical word。 -/
def toCriticalWordOfExtraZero
    {m : ℕ}
    (W : FullFirstCrossingWord m)
    (hExtra : terminalExtraDepth W = 0) :
    CriticalWord m := by
  refine ⟨W.1, W.2.valid, W.2.oddSteps_eq, ?_, ?_⟩
  · have hTotal :=
      twoSteps_eq_criticalTwoDepth_add_terminalExtraDepth W
    rw [hExtra, Nat.add_zero] at hTotal
    exact hTotal
  · intro k hk
    exact W.2.prefixTwoDepth_le_beatty hk

end FullFirstCrossingWord

end Critical
end Collatz3
