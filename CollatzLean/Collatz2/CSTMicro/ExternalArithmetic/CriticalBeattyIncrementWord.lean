import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyLocalSquares

/-!
# Critical Beatty increment word

BHZ 側で使う slope は

  α = log₂ 3 - 1.

したがって BHZ の binary Sturmian word は、`beattyIndex n = floor(n log₂ 3)` の
一段差

  beattyIndex (n+1) - beattyIndex n ∈ {1,2}

から常時存在する `1` を引いた binary word、すなわち

  bit n = 1  iff  beattyIndex (n+1) = beattyIndex n + 2

である。

これは Ferrers boundary 側の `criticalSturmianBit` とは別の mechanical word。
BHZ Proposition 3.3 と `CriticalBeattySquareAt` を接続するときはこちらを使う。

本ファイルでは

* increment は exact に 1 または 2、
* bit equality なら increment equality、
* length-`r` の二つの bit block が一致すれば `CriticalBeattySquareAt s r`

までを証明する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `beattyIndex` は一 odd-column で高々 2 増える。 -/
theorem beattyIndex_succ_le_add_two
    (n : ℕ) :
    beattyIndex (n + 1) ≤ beattyIndex n + 2 := by
  have hUpper := beattyIndex_upper n
  have hCandidate :
      3 ^ (n + 1) ≤
        2 ^ ((beattyIndex n + 2) + 1) := by
    rw [pow_succ]
    calc
      3 ^ n * 3
          ≤ 2 ^ (beattyIndex n + 1) * 3 :=
        Nat.mul_le_mul_right 3 hUpper
      _ ≤ 2 ^ (beattyIndex n + 1) * 4 := by
        exact
          Nat.mul_le_mul_left
            (2 ^ (beattyIndex n + 1))
            (by norm_num : 3 ≤ 4)
      _ = 2 ^ ((beattyIndex n + 1) + 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      _ = 2 ^ ((beattyIndex n + 2) + 1) := by
        congr 1
  exact beattyIndex_le_of_upper hCandidate

/-- 一段の Beatty increment は exact に 1 または 2。 -/
theorem beattyIndex_succ_eq_add_one_or_two
    (n : ℕ) :
    beattyIndex (n + 1) = beattyIndex n + 1 ∨
      beattyIndex (n + 1) = beattyIndex n + 2 := by
  have hLower := beattyIndex_lt_succ n
  have hUpper := beattyIndex_succ_le_add_two n
  omega

/--
BHZ slope `log₂ 3 - 1` の binary increment word。

`true` は Beatty exponent がその step で 2 増えることを表す。
-/
def criticalBeattyIncrementBit
    (n : ℕ) : Bool :=
  decide
    (beattyIndex (n + 1) = beattyIndex n + 2)

@[simp] theorem criticalBeattyIncrementBit_eq_true_iff
    (n : ℕ) :
    criticalBeattyIncrementBit n = true ↔
      beattyIndex (n + 1) = beattyIndex n + 2 := by
  simp [criticalBeattyIncrementBit]

@[simp] theorem criticalBeattyIncrementBit_eq_false_iff
    (n : ℕ) :
    criticalBeattyIncrementBit n = false ↔
      beattyIndex (n + 1) ≠ beattyIndex n + 2 := by
  simp [criticalBeattyIncrementBit]

/-- increment の値を bit から exact に読む。 -/
theorem beattyIncrement_eq_if_incrementBit
    (n : ℕ) :
    beattyIndex (n + 1) - beattyIndex n =
      if criticalBeattyIncrementBit n then 2 else 1 := by
  rcases beattyIndex_succ_eq_add_one_or_two n with hOne | hTwo
  · have hNot :
        beattyIndex (n + 1) ≠ beattyIndex n + 2 := by
      omega
    have hBit :
        criticalBeattyIncrementBit n = false := by
      exact
        (criticalBeattyIncrementBit_eq_false_iff n).2 hNot
    rw [hOne, hBit]
    simp
  · have hBit :
        criticalBeattyIncrementBit n = true := by
      exact
        (criticalBeattyIncrementBit_eq_true_iff n).2 hTwo
    rw [hTwo, hBit]
    simp

/-- 同じ increment bit は同じ Beatty one-step rise を持つ。 -/
theorem beattyIncrement_eq_of_incrementBit_eq
    {i j : ℕ}
    (hBit :
      criticalBeattyIncrementBit i =
        criticalBeattyIncrementBit j) :
    beattyIndex (i + 1) - beattyIndex i =
      beattyIndex (j + 1) - beattyIndex j := by
  rw [
    beattyIncrement_eq_if_incrementBit,
    beattyIncrement_eq_if_incrementBit,
    hBit
  ]

/-- relative Beatty rise の一段 telescoping。 -/
theorem beattyRelativeRise_succ
    (s k : ℕ) :
    beattyIndex (s + (k + 1)) - beattyIndex s =
      (beattyIndex (s + k) - beattyIndex s) +
        (beattyIndex (s + k + 1) -
          beattyIndex (s + k)) := by
  have hBase :
      beattyIndex s ≤ beattyIndex (s + k) := by
    by_cases hk : k = 0
    · subst k
      simp
    · exact
        le_of_lt
          (beattyIndex_strictMono (by omega))
  have hStep :
      beattyIndex (s + k) ≤
        beattyIndex (s + k + 1) := by
    exact
      le_of_lt
        (beattyIndex_lt_succ (s + k))
  have hArg :
      s + (k + 1) = s + k + 1 := by
    omega
  rw [hArg]
  omega

/--
二つの consecutive length-`r` increment-bit block が一致すれば、
relative Beatty rise も全 prefix で一致する。

これが binary BHZ word から `CriticalBeattySquareAt` への generic bridge。
-/
theorem criticalBeattySquareAt_of_incrementBit_blocks
    {s r : ℕ}
    (hr : 0 < r)
    (hBlock :
      ∀ i : ℕ, i < r →
        criticalBeattyIncrementBit (s + i) =
          criticalBeattyIncrementBit (s + r + i)) :
    CriticalBeattySquareAt s r := by
  refine ⟨hr, ?_⟩
  intro k hk
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkLe : k ≤ r := by
        omega
      have hkLt : k < r := by
        omega
      have hPrev := ih hkLe
      have hBit := hBlock k hkLt
      have hInc0 :=
        beattyIncrement_eq_of_incrementBit_eq hBit
      have hInc :
          beattyIndex (s + k + 1) -
              beattyIndex (s + k) =
            beattyIndex (s + r + k + 1) -
              beattyIndex (s + r + k) := by
        simpa [Nat.add_assoc] using hInc0
      have hLeft :=
        beattyRelativeRise_succ s k
      have hRight :=
        beattyRelativeRise_succ (s + r) k
      calc
        beattyIndex (s + (k + 1)) - beattyIndex s
            =
          (beattyIndex (s + k) - beattyIndex s) +
            (beattyIndex (s + k + 1) -
              beattyIndex (s + k)) := hLeft
        _ =
          (beattyIndex (s + r + k) -
              beattyIndex (s + r)) +
            (beattyIndex (s + r + k + 1) -
              beattyIndex (s + r + k)) := by
                rw [hPrev, hInc]
        _ =
          beattyIndex (s + r + (k + 1)) -
            beattyIndex (s + r) := by
              simpa [Nat.add_assoc] using hRight.symm

end ExternalArithmetic
end CSTMicro
end Collatz2
