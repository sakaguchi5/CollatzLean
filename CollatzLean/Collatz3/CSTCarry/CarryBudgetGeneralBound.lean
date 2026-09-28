import CollatzLean.Collatz3.CSTCarry.CarryBudgetChain
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: 任意 initial carry に対する block budget の exact bound

interior block の actual slice は initial carry が必ずしも modulus `M` そのものではない。
そこで `E=M` 特化だけに依存せず、一般 realization

`E + M*C + S = 3^P F`

に対する strict / weak complement budget を final carry の不等式へ exact に変形する。

一般 complement balance

`3^P F + M(D+1) = E + M 3^P + S`

から

* strict budget `S < M(D+1)`
  iff `3^P F < E + 3^P M`,
* weak budget `S ≤ M D`
  iff `3^P F + M ≤ E + 3^P M`

を得る。

これにより block slice の本当の initial carry を保持したまま budget を議論できる。
-/

namespace Collatz3
namespace CSTCarry

namespace CarryRealizes

/-- 任意 initial carry に対する strict complement budget の exact characterization。 -/
theorem complementBudget_iff_scaled_final_lt_initial_add_modulus
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    ComplementBudget M rows digits ↔
      3 ^ rows.length * F < E + 3 ^ rows.length * M := by
  unfold ComplementBudget
  have hBal := h.complement_balance_nat
  have hBal' :
      F * 3 ^ rows.length +
          (M + M * ternaryComplementValue digits) =
        M * 3 ^ rows.length + E +
          ferrersWeightedDefect rows := by
    calc
      F * 3 ^ rows.length +
            (M + M * ternaryComplementValue digits)
          =
        3 ^ rows.length * F +
          M * (ternaryComplementValue digits + 1) := by
            ring
      _ =
        E + M * 3 ^ rows.length +
          ferrersWeightedDefect rows := hBal
      _ =
        M * 3 ^ rows.length + E +
          ferrersWeightedDefect rows := by
            ring
  constructor
  · intro hBudget
    have hBudget' :
        ferrersWeightedDefect rows <
          M + M * ternaryComplementValue digits := by
      calc
        ferrersWeightedDefect rows
            < M * (ternaryComplementValue digits + 1) := hBudget
        _ = M + M * ternaryComplementValue digits := by
          ring
    have hStrict :
        F * 3 ^ rows.length +
            (M + M * ternaryComplementValue digits) <
          (M * 3 ^ rows.length + E) +
            (M + M * ternaryComplementValue digits) := by
      calc
        F * 3 ^ rows.length +
              (M + M * ternaryComplementValue digits)
            =
          M * 3 ^ rows.length + E +
            ferrersWeightedDefect rows := hBal'
        _ <
          M * 3 ^ rows.length + E +
            (M + M * ternaryComplementValue digits) := by
              exact Nat.add_lt_add_left hBudget'
                (M * 3 ^ rows.length + E)
    have hFinal :
        F * 3 ^ rows.length <
          M * 3 ^ rows.length + E := by
      exact Nat.lt_of_add_lt_add_right hStrict
    calc
      3 ^ rows.length * F
          = F * 3 ^ rows.length := by ring
      _ < M * 3 ^ rows.length + E := hFinal
      _ = E + 3 ^ rows.length * M := by ring
  · intro hScaled
    ring_nf at hBal hScaled ⊢
    omega

/-- 任意 initial carry に対する weak complement budget の exact characterization。 -/
theorem weakComplementBudget_iff_scaled_final_add_modulus_le
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    WeakComplementBudget M rows digits ↔
      3 ^ rows.length * F + M ≤ E + 3 ^ rows.length * M := by
  unfold WeakComplementBudget
  have hBal := h.complement_balance_nat
  constructor
  · intro hBudget
    ring_nf at hBal ⊢
    omega
  · intro hScaled
    ring_nf at hBal hScaled ⊢
    omega

/-- initial carry が modulus 以上で final carry が modulus 以下なら weak budget。 -/
theorem weakComplementBudget_of_modulus_le_initial_of_final_le
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F)
    (hInitial : M ≤ E)
    (hFinal : F ≤ M) :
    WeakComplementBudget M rows digits := by
  apply h.weakComplementBudget_iff_scaled_final_add_modulus_le.2
  have hScaled :
      3 ^ rows.length * F ≤ 3 ^ rows.length * M :=
    Nat.mul_le_mul_left _ hFinal
  omega

/-- positive initial carry かつ final carry が modulus 以下なら strict budget まで得られる。 -/
theorem complementBudget_of_initial_pos_of_final_le
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F)
    (hInitial : 0 < E)
    (hFinal : F ≤ M) :
    ComplementBudget M rows digits := by
  apply h.complementBudget_iff_scaled_final_lt_initial_add_modulus.2
  have hScaled :
      3 ^ rows.length * F ≤ 3 ^ rows.length * M :=
    Nat.mul_le_mul_left _ hFinal
  omega

end CarryRealizes

end CSTCarry
end Collatz3
