import CollatzLean.Collatz3.CSTCarry.CarryBudget

/-!
# Collatz3 CSTCarry: complement budget の append telescope

`ferrersWeightedDefect` と `ternaryComplementValue` はともに low-digit-first である。
したがって `xs ++ ys` では `xs` が低位・terminal 側を表し、後半 `ys` は
`3^|xs|` 倍されて合成される。

このファイルでは

* weighted defect の append 公式、
* ternary complement value の append 公式、
* interior block 用の weak complement budget、
* terminal strict budget + interior weak budget の telescope、

だけを薄く置く。
-/

namespace Collatz3
namespace CSTCarry

/--
weighted Ferrers defect の low-digit-first append 公式。

`xs` が低位側なので、後半 `ys` は `3^xs.length` 倍される。
-/
theorem ferrersWeightedDefect_append
    (xs ys : List FerrersRow) :
    ferrersWeightedDefect (xs ++ ys) =
      ferrersWeightedDefect xs +
        3 ^ xs.length * ferrersWeightedDefect ys := by
  induction xs with
  | nil =>
      simp [ferrersWeightedDefect]
  | cons R Rs ih =>
      simp only [List.cons_append, ferrersWeightedDefect_cons, List.length_cons,
        pow_succ]
      rw [ih]
      ring

/--
ternary complement value の low-digit-first append 公式。

`xs` が低位側なので、後半 `ys` は `3^xs.length` 倍される。
-/
theorem ternaryComplementValue_append
    (xs ys : List ℕ) :
    ternaryComplementValue (xs ++ ys) =
      ternaryComplementValue xs +
        3 ^ xs.length * ternaryComplementValue ys := by
  induction xs with
  | nil =>
      simp [ternaryComplementValue]
  | cons a as ih =>
      simp only [List.cons_append, ternaryComplementValue_cons, List.length_cons,
        pow_succ]
      rw [ih]
      ring

/--
interior block 用の weak complement budget。

terminal block の strict budget

`S < M * (D + 1)`

に対し、interior block では `+1` を消した

`S ≤ M * D`

を使う。
-/
def WeakComplementBudget
    (M : ℕ)
    (rows : List FerrersRow)
    (digits : List ℕ) : Prop :=
  ferrersWeightedDefect rows ≤
    M * ternaryComplementValue digits

/--
## complement budget の二 block telescope

low-digit-first の先頭 `rows₀ / digits₀` が terminal 側。

* terminal 側が strict budget
  `S₀ < M(D₀+1)`、
* 後続 block が weak budget
  `S₁ ≤ M D₁`、
* terminal 側の digit 数と row 数が一致、

なら append 全体も strict budget を満たす。

exact に

`S₀ + 3^P S₁ < M(D₀+1) + 3^P M D₁`

を足し合わせるだけである。
-/
theorem complementBudget_telescope
    {M : ℕ}
    {rows₀ rows₁ : List FerrersRow}
    {digits₀ digits₁ : List ℕ}
    (hLen : digits₀.length = rows₀.length)
    (hTerminal : ComplementBudget M rows₀ digits₀)
    (hInterior : WeakComplementBudget M rows₁ digits₁) :
    ComplementBudget M (rows₀ ++ rows₁) (digits₀ ++ digits₁) := by
  unfold ComplementBudget at hTerminal ⊢
  unfold WeakComplementBudget at hInterior
  rw [ferrersWeightedDefect_append, ternaryComplementValue_append]
  rw [hLen]
  have hScaled :
      3 ^ rows₀.length * ferrersWeightedDefect rows₁ ≤
        3 ^ rows₀.length *
          (M * ternaryComplementValue digits₁) :=
    Nat.mul_le_mul_left _ hInterior
  have hCombined :
      ferrersWeightedDefect rows₀ +
          3 ^ rows₀.length * ferrersWeightedDefect rows₁ <
        M * (ternaryComplementValue digits₀ + 1) +
          3 ^ rows₀.length *
            (M * ternaryComplementValue digits₁) :=
    Nat.add_lt_add_of_lt_of_le hTerminal hScaled
  calc
    ferrersWeightedDefect rows₀ +
          3 ^ rows₀.length * ferrersWeightedDefect rows₁
        < M * (ternaryComplementValue digits₀ + 1) +
            3 ^ rows₀.length *
              (M * ternaryComplementValue digits₁) := hCombined
    _ = M *
          (ternaryComplementValue digits₀ +
            3 ^ rows₀.length * ternaryComplementValue digits₁ + 1) := by
          ring

end CSTCarry
end Collatz3
