import CollatzLean.CollatzFirstLayer.Orbit

/-!
# odd-only無限軌道

`CollatzSecondLayer2` は旧 `CollatzSecondLayer` をimportせず、第一層の有限実行
`ExpWord.Runs` だけを用いて無限odd-only軌道を再構成する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 正の2除算指数を用いるodd-onlyコラッツ無限軌道。 -/
structure OddOrbit where
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  exponent_pos : ∀ n, 0 < exponent n
  value_odd : ∀ n, Odd (value n)
  step : ∀ n,
    2 ^ exponent n * value (n + 1) = 3 * value n + 1

namespace OddOrbit

/-- 位置`i`から長さ`m`だけ切り出した指数語。 -/
def segmentWord (O : OddOrbit) (i : ℕ) : ℕ → ExpWord
  | 0 => []
  | m + 1 => O.exponent i :: O.segmentWord (i + 1) m

@[simp] theorem segmentWord_zero (O : OddOrbit) (i : ℕ) :
    O.segmentWord i 0 = [] := rfl

@[simp] theorem segmentWord_succ (O : OddOrbit) (i m : ℕ) :
    O.segmentWord i (m + 1) =
      O.exponent i :: O.segmentWord (i + 1) m := rfl

@[simp] theorem segmentWord_length (O : OddOrbit) (i m : ℕ) :
    (O.segmentWord i m).length = m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [segmentWord, ih]

/-- 長いsegmentの先頭を取ると短いsegmentになる。 -/
theorem segmentWord_take_of_le (O : OddOrbit)
    {i m n : ℕ} (h : m ≤ n) :
    (O.segmentWord i n).take m = O.segmentWord i m := by
  induction m generalizing i n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [segmentWord_succ, List.take_succ_cons]
          rw [ih (i := i + 1) (n := n) (by omega)]

/-- 隣接二区間のsegment wordを連結する。 -/
theorem segmentWord_add (O : OddOrbit) (i m n : ℕ) :
    O.segmentWord i (m + n) =
      O.segmentWord i m ++ O.segmentWord (i + m) n := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      have hlength : m + 1 + n = (m + n) + 1 := by omega
      have hindex : i + 1 + m = i + (m + 1) := by omega
      rw [hlength]
      rw [segmentWord_succ]
      rw [segmentWord_succ, List.cons_append]
      rw [ih (i := i + 1)]
      rw [hindex]

/-- 任意の有限segmentは第一層のactual runである。 -/
theorem runs_segment (O : OddOrbit) (i m : ℕ) :
    Runs (O.segmentWord i m) (O.value i) (O.value (i + m)) := by
  induction m generalizing i with
  | zero => simpa using Runs.nil (O.value i)
  | succ m ih =>
      apply Runs.cons
          (O.exponent_pos i)
          (O.step i)
          (O.value_odd (i + 1))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1)

/-- 任意の有限segmentは第一層のアフィン実現式を満たす。 -/
theorem realizes_segment (O : OddOrbit) (i m : ℕ) :
    Realizes (O.segmentWord i m) (O.value i) (O.value (i + m)) :=
  (O.runs_segment i m).realizes

/-- 任意の軌道値は正。 -/
theorem value_pos (O : OddOrbit) (n : ℕ) : 0 < O.value n := by
  rcases O.value_odd n with ⟨k, hk⟩
  omega

/-- 軌道値が上に有界でないこと。 -/
def Unbounded (O : OddOrbit) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, M < O.value n

/-- 軌道値が最終的に任意の固定上界を越えること。 -/
def EscapesToInfinity (O : OddOrbit) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M < O.value n

end OddOrbit

/-- 非有界odd-only軌道が存在すること。 -/
def HasUnboundedOddOrbit : Prop :=
  ∃ O : OddOrbit, O.Unbounded

end CollatzSecondLayer2
