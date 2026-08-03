import CollatzLean.CollatzFirstLayer.Orbit

/-!
# odd-only無限軌道

第一層の `ExpWord.Runs` は有限実行を表す。
このファイルでは、各有限区間を第一層へ渡せる無限odd-only軌道を定義する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 正の指数を用いるodd-onlyコラッツ無限軌道。 -/
structure OddOrbit where
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  exponent_pos : ∀ n, 0 < exponent n
  value_odd : ∀ n, Odd (value n)
  step : ∀ n,
    2 ^ exponent n * value (n + 1) = 3 * value n + 1

namespace OddOrbit

/-- 位置 `i` から長さ `m` だけ切り出した指数語。 -/
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
  | succ m ih =>
      simp [segmentWord, ih]

/-- 長い区間語の先頭を取ると、短い区間語になる。 -/
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

/-- 任意の有限区間は第一層の `Runs` を満たす。 -/
theorem runs_segment (O : OddOrbit) (i m : ℕ) :
    ExpWord.Runs (O.segmentWord i m)
      (O.value i) (O.value (i + m)) := by
  induction m generalizing i with
  | zero =>
      simpa using ExpWord.Runs.nil (O.value i)
  | succ m ih =>
      apply ExpWord.Runs.cons
          (O.exponent_pos i)
          (O.step i)
          (O.value_odd (i + 1))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1)

/-- 任意の有限区間は第一層のアフィン実現式を満たす。 -/
theorem realizes_segment (O : OddOrbit) (i m : ℕ) :
    Realizes (O.segmentWord i m)
      (O.value i) (O.value (i + m)) :=
  (O.runs_segment i m).realizes

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

end CollatzSecondLayer
