import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.DenominatorWindowCover

/-!
# Strong critical-residue denominator windows

corrected approximant の stronger certified precision

  E'_j = q_j + q_{j+1} - 1

を使うための denominator window。

  L'_j = q_{j-1} + q_j - 1
  U'_j = q_j + q_{j+1} - 1

と置くと

  U'_{j-1} = L'_j

が exact に成立する。

したがって current coarse window と同様に、coverage 自体は純粋な整数算術で閉じる。
外部 Sturmian / continued-fraction 数学が担うのは、各 `j` で `U'_j` まで
2-adic matching が成立することだけである。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- stronger window の lower endpoint `q_{j-1} + q_j - 1`。 -/
def strongDenominatorWindowLower
    (q : ℕ → ℕ) (j : ℕ) : ℕ :=
  q (j - 1) + q j - 1

/-- stronger certified precision endpoint `q_j + q_{j+1} - 1`。 -/
def strongDenominatorWindowUpper
    (q : ℕ → ℕ) (j : ℕ) : ℕ :=
  q j + q (j + 1) - 1

/-- adjacent strong windows は `j>=1` で exact に端点を共有する。 -/
theorem strongDenominatorWindowUpper_prev_eq_lower
    (q : ℕ → ℕ)
    {j : ℕ}
    (hj : 1 ≤ j) :
    strongDenominatorWindowUpper q (j - 1) =
      strongDenominatorWindowLower q j := by
  unfold strongDenominatorWindowUpper strongDenominatorWindowLower
  have h1 : (j - 1) + 1 = j := by omega
  rw [h1]

/-- increasing denominators なら各 strong window は nonempty。 -/
theorem strongDenominatorWindow_nonempty
    (q : ℕ → ℕ)
    (hMono : ∀ n : ℕ, q n ≤ q (n + 1))
    {j : ℕ}
    (hj : 1 ≤ j) :
    strongDenominatorWindowLower q j ≤
      strongDenominatorWindowUpper q j := by
  unfold strongDenominatorWindowLower strongDenominatorWindowUpper
  have hPrev : q (j - 1) ≤ q j := by
    have hEq : (j - 1) + 1 = j := by omega
    simpa [hEq] using hMono (j - 1)
  have hNext : q j ≤ q (j + 1) := hMono j
  omega

/--
`j0` から `j0+n` までの strong window chain は、その両端の間を全て覆う。
-/
theorem exists_strongDenominatorWindow_on_span
    (q : ℕ → ℕ)
    {j0 n e : ℕ}
    (hj0 : 1 ≤ j0)
    (hLow : strongDenominatorWindowLower q j0 ≤ e)
    (hHigh : e ≤ strongDenominatorWindowUpper q (j0 + n)) :
    ∃ j : ℕ,
      j0 ≤ j ∧ j ≤ j0 + n ∧
      strongDenominatorWindowLower q j ≤ e ∧
      e ≤ strongDenominatorWindowUpper q j := by
  induction n with
  | zero =>
      exact ⟨j0, le_rfl, by simp, hLow, by simpa using hHigh⟩
  | succ n ih =>
      by_cases hPrev : e ≤ strongDenominatorWindowUpper q (j0 + n)
      · rcases ih hPrev with ⟨j, hj0j, hjTop, hL, hU⟩
        exact ⟨j, hj0j, by omega, hL, hU⟩
      · have hPrevLt : strongDenominatorWindowUpper q (j0 + n) < e := by
          omega
        let j := j0 + n + 1
        have hj : 1 ≤ j := by
          dsimp [j]
          omega
        have hTouch :
            strongDenominatorWindowUpper q (j - 1) =
              strongDenominatorWindowLower q j :=
          strongDenominatorWindowUpper_prev_eq_lower q hj
        have hjPred : j - 1 = j0 + n := by
          dsimp [j]
        have hNewLow : strongDenominatorWindowLower q j ≤ e := by
          rw [← hTouch, hjPred]
          omega
        have hNewHigh : e ≤ strongDenominatorWindowUpper q j := by
          simpa [j, Nat.add_assoc] using hHigh
        exact ⟨j, by dsimp [j]; omega, by dsimp [j]; omega,
          hNewLow, hNewHigh⟩

/-- finite strong-window chain version。 -/
theorem exists_strongDenominatorWindow_between
    (q : ℕ → ℕ)
    {j0 j1 e : ℕ}
    (hj0 : 1 ≤ j0)
    (hOrder : j0 ≤ j1)
    (hLow : strongDenominatorWindowLower q j0 ≤ e)
    (hHigh : e ≤ strongDenominatorWindowUpper q j1) :
    ∃ j : ℕ,
      j0 ≤ j ∧ j ≤ j1 ∧
      strongDenominatorWindowLower q j ≤ e ∧
      e ≤ strongDenominatorWindowUpper q j := by
  let n := j1 - j0
  have hSum : j0 + n = j1 := by
    dsimp [n]
    omega
  have hHigh' : e ≤ strongDenominatorWindowUpper q (j0 + n) := by
    simpa [hSum] using hHigh
  rcases exists_strongDenominatorWindow_on_span
      q hj0 hLow hHigh' with
    ⟨j, hj0j, hjTop, hL, hU⟩
  refine ⟨j, hj0j, ?_, hL, hU⟩
  rw [hSum] at hjTop
  exact hjTop

/--
`q_j` 自身が cofinal なら strong upper endpoint も cofinal。

`N+1 <= q_j` を選べば、`q_{j+1}` の大きさを使わなくても
`N <= q_j + q_{j+1} - 1` が従う。
-/
theorem strongDenominatorWindowUpper_cofinal_of_q_cofinal
    (q : ℕ → ℕ)
    {j0 : ℕ}
    (hCofinal :
      ∀ N : ℕ, ∃ j : ℕ,
        j0 ≤ j ∧ N ≤ q j) :
    ∀ N : ℕ, ∃ j : ℕ,
      j0 ≤ j ∧ N ≤ strongDenominatorWindowUpper q j := by
  intro N
  rcases hCofinal (N + 1) with ⟨j, hj, hN⟩
  refine ⟨j, hj, ?_⟩
  unfold strongDenominatorWindowUpper
  omega

/-- cofinal strong windows は最初の lower endpoint 以降の全 precision を覆う。 -/
theorem exists_strongDenominatorWindow_cofinal
    (q : ℕ → ℕ)
    {j0 e : ℕ}
    (hj0 : 1 ≤ j0)
    (hLow : strongDenominatorWindowLower q j0 ≤ e)
    (hCofinal :
      ∀ N : ℕ, ∃ j : ℕ,
        j0 ≤ j ∧ N ≤ strongDenominatorWindowUpper q j) :
    ∃ j : ℕ,
      j0 ≤ j ∧
      strongDenominatorWindowLower q j ≤ e ∧
      e ≤ strongDenominatorWindowUpper q j := by
  rcases hCofinal e with ⟨j1, hj1, hUpper⟩
  rcases exists_strongDenominatorWindow_between
      q hj0 hj1 hLow hUpper with
    ⟨j, hj0j, _hjj1, hL, hU⟩
  exact ⟨j, hj0j, hL, hU⟩

/--
strong lower endpoint に入っていれば、positive previous denominator の下で

  2^q_j * 2^(q_{j-1}-1) <= 2^e

が得られる。
-/
theorem strong_twoPow_q_mul_slack_le_twoPow_e
    (q : ℕ → ℕ)
    {j e : ℕ}
    (hPrevPos : 0 < q (j - 1))
    (hWindow : strongDenominatorWindowLower q j ≤ e) :
    2 ^ q j * 2 ^ (q (j - 1) - 1) ≤ 2 ^ e := by
  have hLow : q (j - 1) + q j - 1 ≤ e := by
    simpa [strongDenominatorWindowLower] using hWindow
  have hEq :
      q j + (q (j - 1) - 1) =
        q (j - 1) + q j - 1 := by
    omega
  have hExp : q j + (q (j - 1) - 1) ≤ e := by
    rw [hEq]
    exact hLow
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExp

end ExternalArithmetic
end CSTMicro
end Collatz2
