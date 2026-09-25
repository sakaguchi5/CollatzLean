import CollatzLean.Collatz4.M7.LengthBound

/-!
# Collatz4.M7.ForwardReduction

`4088 ≤ r ≤ 8444`, `r` 偶数を

`n = 8456 - r`

へ移した 2179 個の候補を、`Fin 2179` で重複なく表す。
-/

namespace Collatz4.M7

/-- 偶数候補 `12,14,...,4368` の個数。 -/
def candidateCount : ℕ := 2179

/-- `Fin 2179` による候補 `n` の列挙。 -/
def candidateN (i : Fin candidateCount) : ℕ :=
  12 + 2 * i.1

/-- 候補 `n` の開始自然数 `3^n-1`。 -/
def initialA (i : Fin candidateCount) : ℕ :=
  3 ^ candidateN i - 1

/-- 開始自然数を `(t,u)` 状態へ圧縮する。 -/
def initialState (i : Fin candidateCount) : ForwardState :=
  ForwardState.ofNat (initialA i)

/-- `n` から共通時刻 8456 までに必要な段数。 -/
def remainingSteps (i : Fin candidateCount) : ℕ :=
  targetTime - candidateN i

/-- 候補 `i` の最終状態。 -/
def finalState (i : Fin candidateCount) : ForwardState :=
  run (remainingSteps i) (initialState i)

/-- 最後の1段前 `s=8455` の状態。 -/
def checkpointState (i : Fin candidateCount) : ForwardState :=
  run (8455 - candidateN i) (initialState i)

/-- 目標状態 `(10996, 87*2^2400-1)`。 -/
def targetState : ForwardState :=
  ⟨targetTwoExponent, targetOdd⟩

/-- 候補列の最小値。 -/
theorem candidateN_lower (i : Fin candidateCount) : 12 ≤ candidateN i := by
  simp [candidateN]

/-- 候補列の最大値は 4368。 -/
theorem candidateN_upper (i : Fin candidateCount) : candidateN i ≤ 4368 := by
  have hi : i.1 < 2179 := by
    simpa [candidateCount] using i.2
  simp [candidateN]
  omega

/-- 候補 `n` は全て偶数。 -/
theorem candidateN_even_mod (i : Fin candidateCount) : candidateN i % 2 = 0 := by
  simp [candidateN, Nat.add_mod]

/--
Collatz4 における m=7 の最終前向き候補。

元の指数語側から `12≤n≤4368, n` 偶数まで落ちた後の reduced witness を
この命題で表す。Collatz3 の語彙は使わない。
-/
def M7ForwardCandidate : Prop :=
  ∃ i : Fin candidateCount, finalState i = targetState

end Collatz4.M7
