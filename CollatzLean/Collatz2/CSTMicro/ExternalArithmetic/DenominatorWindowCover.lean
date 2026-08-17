import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelHeightSqueeze

/-!
# Critical residue arithmetic: denominator windows

continued-fraction denominators `q_j` から使う approximation precision が

  E_j = q_{j+1} + q_{j-1}

であるとする。

height squeeze の左端を最適な `q_j + O(log E_j)` まで下げる必要はない。
より粗く

  L_j = q_j + q_{j-2}
  U_j = q_{j+1} + q_{j-1}

と取ると

  U_{j-1} = L_j

が exact に成立する。

したがって interval coverage 自体には Baker/Gouillon は不要。
外部 two-logarithm estimate が担うのは、`e >= L_j` なら
`2^(e-q_j) >= 2^(q_{j-2})` が polynomial height を最終的に凌駕することだけ。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- index `j>=2` の coarse lower endpoint `q_j + q_{j-2}`。 -/
def denominatorWindowLower
    (q : ℕ → ℕ) (j : ℕ) : ℕ :=
  q j + q (j - 2)

/-- index `j>=1` の López--Stoll precision endpoint `q_{j+1}+q_{j-1}`。 -/
def denominatorWindowUpper
    (q : ℕ → ℕ) (j : ℕ) : ℕ :=
  q (j + 1) + q (j - 1)

/-- adjacent coarse windows は `j>=3` で exact に端点を共有する。 -/
theorem denominatorWindowUpper_prev_eq_lower
    (q : ℕ → ℕ)
    {j : ℕ}
    (hj : 3 ≤ j) :
    denominatorWindowUpper q (j - 1) =
      denominatorWindowLower q j := by
  unfold denominatorWindowUpper denominatorWindowLower
  have h1 : (j - 1) + 1 = j := by omega
  have h2 : (j - 1) - 1 = j - 2 := by omega
  rw [h1, h2]

/-- increasing denominators なら各 coarse window は nonempty。 -/
theorem denominatorWindow_nonempty
    (q : ℕ → ℕ)
    (hMono : ∀ n : ℕ, q n ≤ q (n + 1))
    {j : ℕ}
    (hj : 2 ≤ j) :
    denominatorWindowLower q j ≤ denominatorWindowUpper q j := by
  unfold denominatorWindowLower denominatorWindowUpper
  have hA : q j ≤ q (j + 1) := hMono j
  have hB : q (j - 2) ≤ q (j - 1) := by
    have hEq : (j - 2) + 1 = j - 1 := by omega
    simpa [hEq] using hMono (j - 2)
  omega

/--
`j0` から `j0+n` までの denominator window が端点で連結しているため、
最初の lower endpoint と最後の upper endpoint の間にある任意の整数 `e` は、
途中のどれかの window に含まれる。

この被覆には `q` の単調性は不要で、
隣接 window の exact touching
`upper (j-1) = lower j`
だけを用いる。
-/
theorem exists_denominatorWindow_on_span
    (q : ℕ → ℕ)
    {j0 n e : ℕ}
    (hj0 : 3 ≤ j0)
    (hLow : denominatorWindowLower q j0 ≤ e)
    (hHigh : e ≤ denominatorWindowUpper q (j0 + n)) :
    ∃ j : ℕ,
      j0 ≤ j ∧ j ≤ j0 + n ∧
      denominatorWindowLower q j ≤ e ∧
      e ≤ denominatorWindowUpper q j := by
  induction n with
  | zero =>
      exact ⟨j0, le_rfl, by simp, hLow, by simpa using hHigh⟩
  | succ n ih =>
      by_cases hPrev : e ≤ denominatorWindowUpper q (j0 + n)
      · rcases ih hPrev with ⟨j, hj0j, hjTop, hL, hU⟩
        exact ⟨j, hj0j, by omega, hL, hU⟩
      · have hPrevLt : denominatorWindowUpper q (j0 + n) < e := by
          omega
        let j := j0 + n + 1
        have hj : 3 ≤ j := by
          dsimp [j]
          omega
        have hTouch :
            denominatorWindowUpper q (j - 1) =
              denominatorWindowLower q j :=
          denominatorWindowUpper_prev_eq_lower q hj
        have hjPred : j - 1 = j0 + n := by
          dsimp [j]
        have hNewLow : denominatorWindowLower q j ≤ e := by
          rw [← hTouch, hjPred]
          omega
        have hNewHigh : e ≤ denominatorWindowUpper q j := by
          simpa [j, Nat.add_assoc] using hHigh
        exact ⟨j, by dsimp [j]; omega, by dsimp [j]; omega,
          hNewLow, hNewHigh⟩

/--
有限個の touching interval からなる chain は、
最初の lower endpoint と最後の upper endpoint の間の全整数を覆う。

したがって `j0 ≤ j1` のとき、
`lower j0 ≤ e ≤ upper j1` を満たす任意の `e` に対して、
`j0 ≤ j ≤ j1` かつ
`lower j ≤ e ≤ upper j`
を満たす index `j` が存在する。
-/
theorem exists_denominatorWindow_between
    (q : ℕ → ℕ)
    {j0 j1 e : ℕ}
    (hj0 : 3 ≤ j0)
    (hOrder : j0 ≤ j1)
    (hLow : denominatorWindowLower q j0 ≤ e)
    (hHigh : e ≤ denominatorWindowUpper q j1) :
    ∃ j : ℕ,
      j0 ≤ j ∧ j ≤ j1 ∧
      denominatorWindowLower q j ≤ e ∧
      e ≤ denominatorWindowUpper q j := by
  let n := j1 - j0
  have hSum : j0 + n = j1 := by
    dsimp [n]
    omega
  have hHigh' : e ≤ denominatorWindowUpper q (j0 + n) := by
    simpa [hSum] using hHigh
  rcases exists_denominatorWindow_on_span
      q hj0 hLow hHigh' with
    ⟨j, hj0j, hjTop, hL, hU⟩
  refine ⟨j, hj0j, ?_, hL, hU⟩
  rw [hSum] at hjTop
  exact hjTop

/--
denominator window の upper endpoint が cofinal なら、
最初の lower endpoint 以降の任意の precision `e` は、
どれかの denominator window に含まれる。

ここで必要なのは
* 隣接 window が端点で exact に touching していること
* upper endpoint が cofinal であること
の2点だけであり、`q` の単調性はこの被覆定理自体には不要。
-/
theorem exists_denominatorWindow_cofinal
    (q : ℕ → ℕ)
    {j0 e : ℕ}
    (hj0 : 3 ≤ j0)
    (hLow : denominatorWindowLower q j0 ≤ e)
    (hCofinal :
      ∀ N : ℕ, ∃ j : ℕ,
        j0 ≤ j ∧ N ≤ denominatorWindowUpper q j) :
    ∃ j : ℕ,
      j0 ≤ j ∧
      denominatorWindowLower q j ≤ e ∧
      e ≤ denominatorWindowUpper q j := by
  rcases hCofinal e with ⟨j1, hj1, hUpper⟩
  rcases exists_denominatorWindow_between
      q hj0 hj1 hLow hUpper with
    ⟨j, hj0j, _hjj1, hL, hU⟩
  exact ⟨j, hj0j, hL, hU⟩

/--
Baker/Gouillon 側から最終的に必要な denominator-growth output。

これは polynomial one-step growth そのものより用途に近い形で、
`q_{j-2}` dyadic slack が指定した polynomial height を上回ることを要求する。
この interface を二対数線形形式から証明すればよい。
-/
def EventualDyadicSlackDominates
    (q : ℕ → ℕ)
    (Height : ℕ → ℕ → ℕ) : Prop :=
  ∃ j0 : ℕ,
    3 ≤ j0 ∧
    ∀ j : ℕ, j0 ≤ j →
      Height j (denominatorWindowUpper q j) < 2 ^ q (j - 2)

/--
`e` が coarse window 内なら `e-q_j >= q_{j-2}`。
これが height squeeze へ入る elementary bridge。
-/
theorem twoPow_q_mul_slack_le_twoPow_e
    (q : ℕ → ℕ)
    {j e : ℕ}
    (hWindow : denominatorWindowLower q j ≤ e) :
    2 ^ q j * 2 ^ q (j - 2) ≤ 2 ^ e := by
  have hExp : q j + q (j - 2) ≤ e := by
    simpa [denominatorWindowLower] using hWindow
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExp

end ExternalArithmetic
end CSTMicro
end Collatz2
