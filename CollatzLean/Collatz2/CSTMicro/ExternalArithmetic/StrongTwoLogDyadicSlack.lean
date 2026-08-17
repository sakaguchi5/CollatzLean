import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongBoundaryMatch
import Mathlib.Tactic.Ring

/-!
# Strong-window dyadic height squeeze

strong window

  L'_j = q_{j-1} + q_j - 1
  U'_j = q_j + q_{j+1} - 1

では `e >= L'_j` なので、`q_{j-1}>0` の下で

  2^q_j * 2^(q_{j-1}-1) <= 2^e.

したがって外部 Diophantine estimate から最終的に

  H q_j (B(U'_j)+1) < 2^(q_{j-1}-1)

を示せば strong window 全体で height squeeze が成立する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- strong window 全点で必要な Archimedean height squeeze。 -/
def StrongWindowHeightSqueeze
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (B : ℕ → ℕ) : Prop :=
  ∀ j e : ℕ,
    L.start ≤ j →
    strongDenominatorWindowLower L.q j ≤ e →
    e ≤ strongDenominatorWindowUpper L.q j →
    (C.H * L.q j * 2 ^ L.q j) * (B e + 1) < 2 ^ e

/--
strong window 用の最終 dyadic slack packet。

`previous_denominator_pos` は strong lower endpoint から
`q_{j-1}-1` を安全に切り出すためだけに保持する。
actual continued-fraction denominator では自明な positivity fact に対応する。
-/
structure StrongTwoLogDyadicSlack
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (B : ℕ → ℕ) where
  bound_mono : NatBoundMonotone B
  previous_denominator_pos :
    ∀ j : ℕ,
      L.start ≤ j →
      0 < L.q (j - 1)
  dominates :
    ∀ j : ℕ,
      L.start ≤ j →
      C.H * L.q j *
          (B (strongDenominatorWindowUpper L.q j) + 1)
        < 2 ^ (L.q (j - 1) - 1)

namespace StrongTwoLogDyadicSlack

/-- strong dyadic slack から strong window 全体の height squeeze を得る。 -/
theorem toStrongWindowHeightSqueeze
    {L : LopezStollInstantiation}
    {C : ChristoffelHeightInstantiation L}
    {B : ℕ → ℕ}
    (S : StrongTwoLogDyadicSlack C B) :
    StrongWindowHeightSqueeze C B := by
  intro j e hjStart hLower hUpper
  let U := strongDenominatorWindowUpper L.q j
  have hB : B e ≤ B U := by
    apply S.bound_mono
    simpa [U] using hUpper
  have hBsucc : B e + 1 ≤ B U + 1 := by
    omega
  have hCoeff :
      C.H * L.q j * (B e + 1) ≤
        C.H * L.q j * (B U + 1) := by
    exact Nat.mul_le_mul_left (C.H * L.q j) hBsucc
  have hSlackUpper :
      C.H * L.q j * (B U + 1) <
        2 ^ (L.q (j - 1) - 1) := by
    simpa [U] using S.dominates j hjStart
  have hCoeffStrict :
      C.H * L.q j * (B e + 1) <
        2 ^ (L.q (j - 1) - 1) :=
    lt_of_le_of_lt hCoeff hSlackUpper
  have hPowPos : 0 < 2 ^ L.q j := Nat.pow_pos (by omega)
  have hMulStrict :
      2 ^ L.q j *
          (C.H * L.q j * (B e + 1))
        <
      2 ^ L.q j * 2 ^ (L.q (j - 1) - 1) :=
    (Nat.mul_lt_mul_left hPowPos).2 hCoeffStrict
  have hWindowPow :
      2 ^ L.q j * 2 ^ (L.q (j - 1) - 1) ≤ 2 ^ e :=
    strong_twoPow_q_mul_slack_le_twoPow_e
      L.q
      (S.previous_denominator_pos j hjStart)
      hLower
  calc
    (C.H * L.q j * 2 ^ L.q j) * (B e + 1)
        =
      2 ^ L.q j *
        (C.H * L.q j * (B e + 1)) := by
          ring
    _ < 2 ^ L.q j * 2 ^ (L.q (j - 1) - 1) := hMulStrict
    _ ≤ 2 ^ e := hWindowPow

end StrongTwoLogDyadicSlack

end ExternalArithmetic
end CSTMicro
end Collatz2
