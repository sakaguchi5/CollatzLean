import CollatzLean.Collatz2.Orbit.Runs

/-!
# Collatz2: infinite normalized odd-only orbit

無限軌道そのものを exponent / value の列として保持する。
有限区間は `segment` と `Runs` により lossless に切り出す。

future minimum や Expanding / Contracting はまだ導入しない。
-/

namespace Collatz2

/-- 正規化された odd-only Collatz 無限軌道。 -/
structure OddOrbit where
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  exponent_pos : ∀ n, 0 < exponent n
  value_odd : ∀ n, Odd (value n)
  step : ∀ n, 2 ^ exponent n * value (n + 1) = 3 * value n + 1

namespace OddOrbit

/-- 位置 `i` から長さ `m` の exponent word。 -/
def segment (O : OddOrbit) (i : ℕ) : ℕ → Word
  | 0 => []
  | m + 1 => O.exponent i :: O.segment (i + 1) m

@[simp] theorem segment_zero (O : OddOrbit) (i : ℕ) :
    O.segment i 0 = [] := rfl

@[simp] theorem segment_succ (O : OddOrbit) (i m : ℕ) :
    O.segment i (m + 1) = O.exponent i :: O.segment (i + 1) m := rfl

@[simp] theorem segment_length (O : OddOrbit) (i m : ℕ) :
    (O.segment i m).length = m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
      simp [segment, ih]

/-- segment の prefix は短い segment そのもの。 -/
theorem segment_take_of_le
    (O : OddOrbit) {i m n : ℕ}
    (h : m ≤ n) :
    (O.segment i n).take m = O.segment i m := by
  induction m generalizing i n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [segment_succ, List.take_succ_cons]
          rw [ih (i := i + 1) (n := n) (by omega)]

/-- 隣接する二つの segment は append で exact に連結する。 -/
theorem segment_add (O : OddOrbit) (i m n : ℕ) :
    O.segment i (m + n) =
      O.segment i m ++ O.segment (i + m) n := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      have hlength : m + 1 + n = (m + n) + 1 := by omega
      have hindex : i + 1 + m = i + (m + 1) := by omega
      rw [hlength, segment_succ, segment_succ, List.cons_append,
        ih (i := i + 1), hindex]

/-- 任意の有限 segment は normalized odd-only run。 -/
theorem runsSegment (O : OddOrbit) (i m : ℕ) :
    Runs (O.segment i m) (O.value i) (O.value (i + m)) := by
  induction m generalizing i with
  | zero =>
      simpa using Runs.nil (O.value i)
  | succ m ih =>
      apply Runs.cons
        (O.exponent_pos i)
        (O.step i)
        (O.value_odd (i + 1))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1)

/-- 任意の有限 segment は affine realization を与える。 -/
theorem realizesSegment (O : OddOrbit) (i m : ℕ) :
    Word.Realizes
      (O.segment i m)
      (O.value i)
      (O.value (i + m)) :=
  (O.runsSegment i m).realizes

/-- 軌道値は正。 -/
theorem value_pos (O : OddOrbit) (n : ℕ) :
    0 < O.value n := by
  rcases O.value_odd n with ⟨k, hk⟩
  omega

/-- 軌道値が上に有界でない。 -/
def Unbounded (O : OddOrbit) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, M < O.value n

/-- 軌道値が最終的に任意の固定上界を越える。 -/
def EscapesToInfinity (O : OddOrbit) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M < O.value n

end OddOrbit

/-- 非有界 normalized odd-only 軌道が存在する。 -/
def HasUnboundedOddOrbit : Prop :=
  ∃ O : OddOrbit, O.Unbounded

end Collatz2
