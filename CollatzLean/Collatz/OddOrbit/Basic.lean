import CollatzLean.Collatz.FiniteOrbit.Runs

/-!
# odd-only無限軌道
-/

namespace Collatz

/-- 正の2除算指数を用いるodd-only Collatz無限軌道。 -/
structure OddOrbit where
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  exponent_pos : ∀ n, 0 < exponent n
  value_odd : ∀ n, Odd (value n)
  step : ∀ n, 2 ^ exponent n * value (n + 1) = 3 * value n + 1

namespace OddOrbit

/-- 位置`i`から長さ`m`を切り出した指数語。 -/
def segment (O : OddOrbit) (i : ℕ) : ℕ → Collatz.Word
  | 0 => []
  | m + 1 => O.exponent i :: O.segment (i + 1) m

@[simp] theorem segment_zero (O : OddOrbit) (i : ℕ) : O.segment i 0 = [] := rfl

@[simp] theorem segment_succ (O : OddOrbit) (i m : ℕ) :
    O.segment i (m + 1) = O.exponent i :: O.segment (i + 1) m := rfl

@[simp] theorem segment_length (O : OddOrbit) (i m : ℕ) :
    (O.segment i m).length = m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [segment, ih]

/-- segmentのprefix。 -/
theorem segment_take_of_le (O : OddOrbit)
    {i m n : ℕ} (h : m ≤ n) :
    (O.segment i n).take m = O.segment i m := by
  induction m generalizing i n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [segment_succ, List.take_succ_cons]
          rw [ih (i := i + 1) (n := n) (by omega)]

/-- 隣接二区間の連結。 -/
theorem segment_add (O : OddOrbit) (i m n : ℕ) :
    O.segment i (m + n) = O.segment i m ++ O.segment (i + m) n := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      have hlength : m + 1 + n = (m + n) + 1 := by omega
      have hindex : i + 1 + m = i + (m + 1) := by omega
      rw [hlength, segment_succ, segment_succ, List.cons_append, ih (i := i + 1), hindex]

/-- 任意の有限segmentはactual run。 -/
theorem runsSegment (O : OddOrbit) (i m : ℕ) :
    Word.Runs (O.segment i m) (O.value i) (O.value (i + m)) := by
  induction m generalizing i with
  | zero => simpa using Word.Runs.nil (O.value i)
  | succ m ih =>
      apply Word.Runs.cons (O.exponent_pos i) (O.step i) (O.value_odd (i + 1))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i := i + 1)

/-- 任意segmentはアフィン実現式を満たす。 -/
theorem realizesSegment (O : OddOrbit) (i m : ℕ) :
    (O.segment i m).Realizes (O.value i) (O.value (i + m)) :=
  (O.runsSegment i m).realizes

/-- 軌道値は正。 -/
theorem value_pos (O : OddOrbit) (n : ℕ) : 0 < O.value n := by
  rcases O.value_odd n with ⟨k, hk⟩
  omega

/-- 軌道値が上に有界でない。 -/
def Unbounded (O : OddOrbit) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, M < O.value n

/-- 軌道値が最終的に任意の固定上界を越える。 -/
def EscapesToInfinity (O : OddOrbit) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M < O.value n

end OddOrbit

/-- 非有界odd-only軌道が存在する。 -/
def HasUnboundedOddOrbit : Prop := ∃ O : OddOrbit, O.Unbounded

end Collatz
