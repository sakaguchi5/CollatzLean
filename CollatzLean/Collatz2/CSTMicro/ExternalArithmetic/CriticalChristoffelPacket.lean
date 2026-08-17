import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalContinuedFractionData

/-!
# Explicit corrected Christoffel packet

critical convergent `(p_j,q_j)` に対する Christoffel affine numerator を
有限 fold として explicit に定義し、odd/even corrected packet

odd j:
  P_j = φ_j
  Q_j = 3^p_j - 2^q_j

even j:
  P_j = 2^(q_j-1) - 3 φ_j
  Q_j = 3 (2^q_j - 3^p_j)

をそのまま Lean object にする。

`Q_j` の odd 性と nonnegative exact equality 排除は、
この explicit formula から最終的に証明すべき pure arithmetic facts として
`CriticalChristoffelPacket` に隔離する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Christoffel word `1 z 0` に対応する affine numerator の explicit finite sum。

数学的には

  φ(p,q) = Σ_{0 <= i < p} 3^(p-1-i) 2^floor(i q / p)

だが、Lean では sigma notation を使わず `List.range` の fold で持つ。
-/
def criticalChristoffelPhi
    (p q : ℕ) : ℤ :=
  (List.range p).foldl
    (fun acc i =>
      acc +
        (3 : ℤ) ^ (p - 1 - i) *
          (2 : ℤ) ^ ((i * q) / p))
    0

/-- index `j` の explicit Christoffel numerator `φ_j`。 -/
def criticalChristoffelPhiAt
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  criticalChristoffelPhi (D.p j) (D.q j)

/-- corrected numerator `P_j`。 -/
def correctedChristoffelP
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  if j % 2 = 1 then
    criticalChristoffelPhiAt D j
  else
    (2 : ℤ) ^ (D.q j - 1) -
      3 * criticalChristoffelPhiAt D j

/-- corrected denominator `Q_j`。 -/
def correctedChristoffelQ
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  if j % 2 = 1 then
    (3 : ℤ) ^ D.p j - (2 : ℤ) ^ D.q j
  else
    3 * ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j)

@[simp] theorem correctedChristoffelP_odd
    (D : CriticalContinuedFractionData)
    {j : ℕ}
    (hj : j % 2 = 1) :
    correctedChristoffelP D j =
      criticalChristoffelPhiAt D j := by
  simp [correctedChristoffelP, hj]

@[simp] theorem correctedChristoffelQ_odd
    (D : CriticalContinuedFractionData)
    {j : ℕ}
    (hj : j % 2 = 1) :
    correctedChristoffelQ D j =
      (3 : ℤ) ^ D.p j - (2 : ℤ) ^ D.q j := by
  simp [correctedChristoffelQ, hj]

@[simp] theorem correctedChristoffelP_even
    (D : CriticalContinuedFractionData)
    {j : ℕ}
    (hj : j % 2 = 0) :
    correctedChristoffelP D j =
      (2 : ℤ) ^ (D.q j - 1) -
        3 * criticalChristoffelPhiAt D j := by
  have hne : j % 2 ≠ 1 := by omega
  simp [correctedChristoffelP, hne]

@[simp] theorem correctedChristoffelQ_even
    (D : CriticalContinuedFractionData)
    {j : ℕ}
    (hj : j % 2 = 0) :
    correctedChristoffelQ D j =
      3 * ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) := by
  have hne : j % 2 ≠ 1 := by omega
  simp [correctedChristoffelQ, hne]

/--
explicit corrected formulas を actual `LopezStollInstantiation` にするために
残る pure integer certificate。
-/
structure CriticalChristoffelPacket
    (D : CriticalContinuedFractionData) where
  /-- corrected denominator は 2-adic unit。 -/
  Q_odd :
    ∀ j : ℕ,
      ¬ (2 : ℤ) ∣ correctedChristoffelQ D j

  /-- corrected rational `-P_j/Q_j` は nonnegative integer ではない。 -/
  exact_nonnegative_excluded :
    ∀ j : ℕ,
      ExcludesNonnegativeExact
        (correctedChristoffelP D j)
        (correctedChristoffelQ D j)

namespace CriticalChristoffelPacket

/-- explicit corrected packet family を既存 actual-family interface へ落とす。 -/
def toLopezStollInstantiation
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D) :
    LopezStollInstantiation := {
  q := D.q
  P := correctedChristoffelP D
  Q := correctedChristoffelQ D
  start := D.start
  start_ge_three := D.start_ge_three
  q_mono := D.q_mono
  q_cofinal := D.q_cofinal
  Q_odd := C.Q_odd
  exact_nonnegative_excluded := C.exact_nonnegative_excluded
}

@[simp] theorem toLopezStollInstantiation_q
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D)
    (j : ℕ) :
    C.toLopezStollInstantiation.q j = D.q j := rfl

@[simp] theorem toLopezStollInstantiation_P
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D)
    (j : ℕ) :
    C.toLopezStollInstantiation.P j =
      correctedChristoffelP D j := rfl

@[simp] theorem toLopezStollInstantiation_Q
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D)
    (j : ℕ) :
    C.toLopezStollInstantiation.Q j =
      correctedChristoffelQ D j := rfl

@[simp] theorem toLopezStollInstantiation_start
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D) :
    C.toLopezStollInstantiation.start = D.start := rfl

/-- continued-fraction strict growth は既存 fallback bridge の strictness を満たす。 -/
theorem toPreviousDenominatorStrict
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D) :
    PreviousDenominatorStrict C.toLopezStollInstantiation := by
  intro j hj
  exact D.q_strict_previous j hj

end CriticalChristoffelPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
