import CollatzLean.Collatz2.CSTMicro.CarryGeometry.AdmissibleSturmianProfile
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnProfileResidualLedger

/-!
# Profile cost closed form

`ColumnLayerCostDynamics` の full odd-scale cell identityでは、cell cost の mod-gap 部分は

  2^(beta_k-j-1) * 3^(m-k-1)

という canonical power termになる。

ここでは actual carry / quotient を一切使わず、この power term を final profile 全体で積分する。
column `k` の height を `h(k)` とすると

  sum_{j<h(k)} 2^(beta_k-j-1)
    = 2^beta_k - 2^(beta_k-h(k))

なので二重和は exact に

  sum_k
    (2^beta_k - 2^(beta_k-h(k))) * 3^(m-k-1)

へ閉じる。

これは later Sturmian/Ostrowski block decomposition へ渡す integer closed form。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators

/-- profile cell `(k,j)` の natural scaled power term。 -/
def profileDyadicCellTerm
    (m k j : ℕ) : ℕ :=
  2 ^ (beattyIndex k - j - 1) *
    3 ^ (m - (k + 1))

/-- profile 全 cell の scaled power 二重和。 -/
def profileDyadicCellNumerator
    (m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  columnProfileSum m h
    (fun k j => profileDyadicCellTerm m k j)

/-- 一 column を finite geometric sum で畳んだ closed term。 -/
def profileDyadicClosedColumn
    (m k depth : ℕ) : ℕ :=
  (2 ^ beattyIndex k - 2 ^ (beattyIndex k - depth)) *
    3 ^ (m - (k + 1))

/-- closed column terms の全和。 -/
def profileDyadicClosedNumerator
    (m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  Finset.sum (Finset.range m)
    (fun k => profileDyadicClosedColumn m k (h k))

/--
下降する 2 冪の finite geometric sum。

  sum_{j<h} 2^(b-j-1) = 2^b - 2^(b-h),   h <= b.
-/
theorem sum_twoPow_descending
    {b h : ℕ}
    (hh : h ≤ b) :
    Finset.sum (Finset.range h)
        (fun j => 2 ^ (b - j - 1)) =
      2 ^ b - 2 ^ (b - h) := by
  induction h with
  | zero =>
      simp
  | succ h ih =>
      have hh0 : h ≤ b := by omega
      have hhb : h + 1 ≤ b := by omega
      rw [Finset.sum_range_succ, ih hh0]
      have hSub : b - h = (b - (h + 1)) + 1 := by omega
      have hLast : b - h - 1 = b - (h + 1) := by omega
      rw [hLast, hSub, pow_succ]
      have hPowLe :
          2 ^ ((b - (h + 1)) + 1) ≤ 2 ^ b := by
        apply Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
        omega
      rw [pow_succ] at hPowLe
      omega

/-- 一 column の cell sum は `2^beta - 2^(beta-depth)` に exact に閉じる。 -/
theorem profileDyadicColumnSum_eq_closed
    {m k depth : ℕ}
    (hDepth : depth ≤ beattyIndex k) :
    Finset.sum (Finset.range depth)
        (fun j => profileDyadicCellTerm m k j) =
      profileDyadicClosedColumn m k depth := by
  unfold profileDyadicCellTerm profileDyadicClosedColumn
  calc
    Finset.sum (Finset.range depth)
        (fun j => 2 ^ (beattyIndex k - j - 1) *
          3 ^ (m - (k + 1)))
        =
      (Finset.sum (Finset.range depth)
        (fun j => 2 ^ (beattyIndex k - j - 1))) *
          3 ^ (m - (k + 1)) := by
            rw [Finset.sum_mul]
    _ =
      (2 ^ beattyIndex k - 2 ^ (beattyIndex k - depth)) *
        3 ^ (m - (k + 1)) := by
          rw [sum_twoPow_descending hDepth]

/--
admissible profile では全 cell の二重和が closed numerator と exact に一致する。
-/
theorem profileDyadicCellNumerator_eq_closed
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h) :
    profileDyadicCellNumerator m h =
      profileDyadicClosedNumerator m h := by
  unfold profileDyadicCellNumerator profileDyadicClosedNumerator columnProfileSum
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < m := Finset.mem_range.mp hk
  exact profileDyadicColumnSum_eq_closed (A.depth_le hkLt)

/--
Stage 1 の integer power term は Stage 3 の natural cell term の cast と一致する。
-/
theorem columnLayerScaledPowerTerm_eq_profileDyadicCellTerm_cast
    (m k j : ℕ) :
    columnLayerScaledPowerTerm m k j =
      (profileDyadicCellTerm m k j : ℤ) := by
  unfold columnLayerScaledPowerTerm profileDyadicCellTerm
  rw [columnLayerPosition_eq_beattyIndex]
  push_cast
  rfl

/-- closed form を integer 側でそのまま使うための cast wrapper。 -/
theorem profileDyadicCellNumerator_cast_eq_closed
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h) :
    (profileDyadicCellNumerator m h : ℤ) =
      (profileDyadicClosedNumerator m h : ℤ) := by
  exact congrArg (fun n : ℕ => (n : ℤ))
    (profileDyadicCellNumerator_eq_closed A)

end CSTMicro
end Collatz2
