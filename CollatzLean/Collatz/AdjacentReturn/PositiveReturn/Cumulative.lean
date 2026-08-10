import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.Core

/-!
# positive return chain の累積算術

個々の first-crossing return だけでなく、隣接 future minimum の drift を
chain 全体で telescope する。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace CanonicalChain

/-- 先頭 `n` block の adjacent value gap の累積。 -/
def cumulativeGap {O : OddOrbit} (C : CanonicalChain O) : ℕ → ℕ
  | 0 => 0
  | n + 1 => C.cumulativeGap n + (C.state n).valueGap

/-- 先頭 `n` block の first-crossing 長の累積。 -/
def cumulativeLength {O : OddOrbit} (C : CanonicalChain O) : ℕ → ℕ
  | 0 => 0
  | n + 1 => C.cumulativeLength n + (C.firstCrossing n).length

@[simp] theorem cumulativeGap_zero
    {O : OddOrbit} (C : CanonicalChain O) : C.cumulativeGap 0 = 0 := rfl

@[simp] theorem cumulativeGap_succ
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    C.cumulativeGap (n + 1) =
      C.cumulativeGap n + (C.state n).valueGap := rfl

@[simp] theorem cumulativeLength_zero
    {O : OddOrbit} (C : CanonicalChain O) : C.cumulativeLength 0 = 0 := rfl

@[simp] theorem cumulativeLength_succ
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    C.cumulativeLength (n + 1) =
      C.cumulativeLength n + (C.firstCrossing n).length := rfl

/-- adjacent gap の累積は最初の source から第 `n` start までの exact drift。 -/
theorem source_add_cumulativeGap
    {O : OddOrbit} (C : CanonicalChain O) :
    ∀ n : ℕ,
      C.core.source + C.cumulativeGap n = (C.state n).startValue := by
  intro n
  induction n with
  | zero =>
      simp [CanonicalContractingChain.source, state]
  | succ n ih =>
      rw [cumulativeGap_succ]
      calc
        C.core.source +
            (C.cumulativeGap n + (C.state n).valueGap)
            =
          (C.core.source + C.cumulativeGap n) +
            (C.state n).valueGap := by omega
        _ = (C.state n).startValue + (C.state n).valueGap := by rw [ih]
        _ = (C.state n).nextValue :=
          (C.state n).nextValue_eq_startValue_add_valueGap.symm
        _ = (C.state (n + 1)).startValue :=
          C.core.nextValue_eq_next_startValue n

/-- 各 adjacent value gap 自体も first-crossing length の 1/3 未満。 -/
theorem three_mul_valueGap_lt_crossingLength
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    3 * (C.state n).valueGap < (C.firstCrossing n).length := by
  have hle := (C.firstCrossing n).valueGap_le_returnGap
  have hmul :
      3 * (C.state n).valueGap ≤
        3 * (C.firstCrossing n).returnGap :=
    Nat.mul_le_mul_left 3 hle
  exact lt_of_le_of_lt hmul (C.firstCrossing n).three_mul_returnGap_lt_length

/-- 累積 drift に対する非狭義版。 -/
theorem three_mul_cumulativeGap_le_cumulativeLength
    {O : OddOrbit} (C : CanonicalChain O) :
    ∀ n : ℕ,
      3 * C.cumulativeGap n ≤ C.cumulativeLength n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cumulativeGap_succ, cumulativeLength_succ]
      have hlocal := C.three_mul_valueGap_lt_crossingLength n
      omega

/-- 一つ以上 block を取れば累積 drift にも strict `3*gap < length` が残る。 -/
theorem three_mul_cumulativeGap_lt_cumulativeLength
    {O : OddOrbit} (C : CanonicalChain O)
    {n : ℕ} (hn : 0 < n) :
    3 * C.cumulativeGap n < C.cumulativeLength n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 :=
    ⟨n - 1, by omega⟩
  rw [cumulativeGap_succ, cumulativeLength_succ]
  have hprev := C.three_mul_cumulativeGap_le_cumulativeLength m
  have hlocal := C.three_mul_valueGap_lt_crossingLength m
  omega

end CanonicalChain
end PositiveReturn
end AdjacentReturn
end Collatz
