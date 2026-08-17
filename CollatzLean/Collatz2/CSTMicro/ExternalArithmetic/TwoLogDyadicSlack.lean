import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelHeightBound
import Mathlib.Tactic.Ring

/-!
# Diophantine denominator growth -> dyadic height squeeze

coarse denominator window

  L_j = q_j + q_{j-2}
  U_j = q_{j+1} + q_{j-1}

では `e ≥ L_j` だから

  2^q_j * 2^q_{j-2} ≤ 2^e.

したがって、外部の two-logarithm / irrationality-measure input から
continued-fraction denominator growth を制御し、最終的に

  H q_j (B(U_j)+1) < 2^q_{j-2}

が得られれば、任意の `e ∈ [L_j,U_j]` について

  H q_j 2^q_j (B(e)+1) < 2^e

が従う。

ここで必要なのは特定の Baker / Gouillon 定理そのものではなく、
最終的な dyadic domination だけである。
したがって将来 Rhin / Wang--Wu 型の `log 2 / log 3` 専用評価へ差し替えても
下流の theorem は変わらない。

隣接 window の coverage 自体には外部 Diophantine estimate は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- residue bound function が単調であること。 -/
def NatBoundMonotone (B : ℕ → ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ≤ b → B a ≤ B b

/--
外部 Diophantine estimate から必要な最終 dyadic slack。

`start` の具体値はここでは固定しない。
選択した explicit two-log / irrationality-measure theorem から denominator growth を評価し、
その有効開始点以降でこの inequality を示せばよい。
-/
structure TwoLogDyadicSlack
    (F : CriticalResidueApproximationFamily)
    (B : ℕ → ℕ) where
  bound_mono : NatBoundMonotone B
  dominates :
    ∀ j : ℕ,
      F.start ≤ j →
      F.H * F.q j *
          (B (denominatorWindowUpper F.q j) + 1)
        < 2 ^ F.q (j - 2)

namespace TwoLogDyadicSlack

/--
dyadic slack は abstract separation engine の `WindowHeightSqueeze`
を与える。
-/
theorem toWindowHeightSqueeze
    {F : CriticalResidueApproximationFamily}
    {B : ℕ → ℕ}
    (S : TwoLogDyadicSlack F B) :
    F.WindowHeightSqueeze B := by
  intro j e hjStart hLower hUpper
  let U := denominatorWindowUpper F.q j
  have hB :
      B e ≤ B U := by
    apply S.bound_mono
    simpa [U] using hUpper
  have hBsucc :
      B e + 1 ≤ B U + 1 := by
    omega
  have hCoeff :
      F.H * F.q j * (B e + 1) ≤
        F.H * F.q j * (B U + 1) := by
    exact
      Nat.mul_le_mul_left
        (F.H * F.q j)
        hBsucc
  have hSlackUpper :
      F.H * F.q j * (B U + 1) <
        2 ^ F.q (j - 2) := by
    simpa [U] using S.dominates j hjStart
  have hCoeffStrict :
      F.H * F.q j * (B e + 1) <
        2 ^ F.q (j - 2) :=
    lt_of_le_of_lt hCoeff hSlackUpper
  have hPowPos :
      0 < 2 ^ F.q j := Nat.pow_pos (by omega)
  have hMulStrict :
      2 ^ F.q j *
          (F.H * F.q j * (B e + 1))
        <
      2 ^ F.q j * 2 ^ F.q (j - 2) :=
    (Nat.mul_lt_mul_left hPowPos).2 hCoeffStrict
  have hWindowPow :
      2 ^ F.q j * 2 ^ F.q (j - 2) ≤ 2 ^ e :=
    twoPow_q_mul_slack_le_twoPow_e F.q hLower
  calc
    (F.H * F.q j * 2 ^ F.q j) * (B e + 1)
        =
      2 ^ F.q j *
        (F.H * F.q j * (B e + 1)) := by
          ring
    _ <
      2 ^ F.q j * 2 ^ F.q (j - 2) :=
        hMulStrict
    _ ≤ 2 ^ e := hWindowPow

end TwoLogDyadicSlack

end ExternalArithmetic
end CSTMicro
end Collatz2
