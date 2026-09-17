import CollatzLean.Collatz3.Binary.Defect
import CollatzLean.Collatz3.Mersenne.Basic

import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: one-zero near-Mersenne family

二進表示で `0` がちょうど一つだけ現れる族を、減算を primitive definition に入れず

`x + 1 = 2^k * (2^n - 1)`

で定義する。

LSB-first binary word は

`1^k 0 1^(n-1)`

であり、ここから alternating weight と zero defect を derived theorem として得る。
-/

namespace Collatz3
namespace Mersenne

/--
one-zero near-Mersenne source。

`k` は唯一の `0` の位置、`n` はその位置から bit length 上端までの幅。
-/
def IsOneZeroSource
    (k n x : ℕ) : Prop :=
  0 < k ∧
    2 ≤ n ∧
    x + 1 = 2 ^ k * (2 ^ n - 1)

namespace IsOneZeroSource

/-- zero position は正。 -/
theorem position_pos
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    0 < k := h.1

/-- zero より上には少なくとも 1 bit の `1` がある。 -/
theorem width_ge_two
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    2 ≤ n := h.2.1

/-- one-zero source の defining equation。 -/
theorem equation
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    x + 1 = 2 ^ k * (2 ^ n - 1) := h.2.2

/-- defining equation を減算なしの `2^(k+n)` 形へ戻す。 -/
theorem add_one_add_missingBit_eq_twoPow
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    x + 1 + 2 ^ k = 2 ^ (k + n) := by
  have hPowPos : 0 < 2 ^ n := Arithmetic.twoPow_pos n
  have hOneLe : 1 ≤ 2 ^ n := by omega
  have hSub : (2 ^ n - 1) + 1 = 2 ^ n :=
    Nat.sub_add_cancel hOneLe
  calc
    x + 1 + 2 ^ k
        = 2 ^ k * (2 ^ n - 1) + 2 ^ k := by rw [h.equation]
    _ = 2 ^ k * ((2 ^ n - 1) + 1) := by ring
    _ = 2 ^ k * 2 ^ n := by rw [hSub]
    _ = 2 ^ (k + n) := by rw [pow_add]

/--
exit equation と odd endpoint が与えられれば、one-zero source はそのまま `BlockData` になる。
-/
theorem blockData
    {k n r x y : ℕ}
    (h : IsOneZeroSource k n x)
    (hr : 0 < r)
    (hy : Odd y)
    (hExit :
      2 ^ r * y + 1 = 3 ^ k * (2 ^ n - 1)) :
    BlockData k r (2 ^ n - 1) x y := by
  exact ⟨h.position_pos, hr, hy, h.equation, hExit⟩

end IsOneZeroSource

/-- one-zero source の canonical LSB-first binary word。 -/
def oneZeroWord (k n : ℕ) : List Bool :=
  List.replicate k true ++
    false :: List.replicate (n - 1) true

/-- one-zero word の長さは `k+n`。 -/
theorem oneZeroWord_length
    {k n : ℕ}
    (hn : 1 ≤ n) :
    (oneZeroWord k n).length = k + n := by
  simp [oneZeroWord]
  omega

/--
one-zero word の値を defining equation と同じ減算なしの形で表す。
-/
theorem oneZeroWord_value_add_one_add_missingBit
    {k n : ℕ}
    (hn : 1 ≤ n) :
    Binary.valueLSB (oneZeroWord k n) + 1 + 2 ^ k =
      2 ^ (k + n) := by
  let A : ℕ := Binary.valueLSB (List.replicate k true)
  let B : ℕ := Binary.valueLSB (List.replicate (n - 1) true)
  have hA : A + 1 = 2 ^ k := by
    simpa [A] using Binary.valueLSB_replicate_true_add_one k
  have hB : B + 1 = 2 ^ (n - 1) := by
    simpa [B] using Binary.valueLSB_replicate_true_add_one (n - 1)
  have hVal :
      Binary.valueLSB (oneZeroWord k n) =
        A + 2 ^ k * (2 * B) := by
    simp [oneZeroWord, Binary.valueLSB_append, A, B]
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hTwoPow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    calc
      2 * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := by ring
      _ = 2 ^ ((n - 1) + 1) := by rw [pow_succ]
      _ = 2 ^ n := by rw [hnEq]
  calc
    Binary.valueLSB (oneZeroWord k n) + 1 + 2 ^ k
        = (A + 1) + 2 ^ k * (2 * B) + 2 ^ k := by
            rw [hVal]
            ring
    _ = 2 ^ k + 2 ^ k * (2 * B) + 2 ^ k := by rw [hA]
    _ = 2 ^ k * (2 * (B + 1)) := by ring
    _ = 2 ^ k * (2 * 2 ^ (n - 1)) := by rw [hB]
    _ = 2 ^ k * 2 ^ n := by rw [hTwoPow]
    _ = 2 ^ (k + n) := by rw [pow_add]

/-- one-zero defining equation は canonical one-zero word を実現する。 -/
theorem IsOneZeroSource.represents_oneZeroWord
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    Binary.RepresentsAtLength (oneZeroWord k n) x (k + n) := by
  have hn : 1 ≤ n := by
    unfold IsOneZeroSource at h
    omega
  refine ⟨oneZeroWord_length hn, ?_⟩
  have hWord := oneZeroWord_value_add_one_add_missingBit (k := k) hn
  have hSource := h.add_one_add_missingBit_eq_twoPow
  omega

/-- one-zero word には `0` がちょうど一つだけある。 -/
theorem oneZeroWord_zeroCount (k n : ℕ) :
    Binary.zeroCount (oneZeroWord k n) = 1 := by
  simp [oneZeroWord, Binary.zeroCount_append]

/-- one-zero source の zero defect は exactly `1`。 -/
theorem IsOneZeroSource.hasZeroDefect
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    Binary.HasZeroDefect x 1 (k + n) := by
  refine ⟨oneZeroWord k n, h.represents_oneZeroWord, ?_⟩
  exact oneZeroWord_zeroCount k n

/--
one-zero source は canonical one-zero word が持つ alternating weight を実現する。

閉形式はここで primitive にせず、必要な parity-specialized formula は後段で導く。
-/
theorem IsOneZeroSource.hasAlternatingWeight
    {k n x : ℕ}
    (h : IsOneZeroSource k n x) :
    Binary.HasAlternatingWeight
      x
      (Binary.evenOneCount (oneZeroWord k n))
      (Binary.oddOneCount (oneZeroWord k n))
      (k + n) := by
  exact Binary.HasAlternatingWeight.of_representation h.represents_oneZeroWord

end Mersenne
end Collatz3
