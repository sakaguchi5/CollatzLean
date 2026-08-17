import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.LopezStollInstantiation

/-!
# López--Stoll / Christoffel Archimedean height instantiation

前段 `LopezStollInstantiation` の actual `P_j,Q_j` に

  |P_j|, |Q_j| ≤ H q_j 2^q_j

という一様 bound を載せる。

数学的には Christoffel numerator

  φ(v_j)
    = Σ 3^(p_j-1-i) 2^floor(i q_j / p_j)

の各項が `< 2^q_j` で、項数 `p_j ≤ q_j` であることから
`φ(v_j) < q_j 2^q_j` を得て、
odd/even corrected formulas を通して fixed constant `H`
（例えば粗い `H=4`）へ押し込む層に対応する。

ここは two-logarithm theorem ではなく、corrected numerator formula と
Christoffel balance から得る elementary Archimedean estimate の層である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
actual López--Stoll family に対する uniform Christoffel height theorem。

ここが Christoffel balance / corrected numerator formula を移植する場所。
-/
structure ChristoffelHeightInstantiation
    (L : LopezStollInstantiation) where
  H : ℕ
  height :
    ∀ j : ℕ,
      HasChristoffelHeightBound
        H (L.q j) (L.P j) (L.Q j)

namespace ChristoffelHeightInstantiation

/--
López--Stoll arithmetic data と uniform height theorem を合わせて、
abstract separation engine が要求する family を構成する。
-/
def toApproximationFamily
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L) :
    CriticalResidueApproximationFamily := {
  q := L.q
  packet := L.packet
  H := C.H
  start := L.start
  start_ge_three := L.start_ge_three
  q_mono := L.q_mono
  packet_q := by
    intro j
    rfl
  packet_precision := by
    intro j
    exact L.packet_precision j
  height := by
    intro j
    simpa [LopezStollInstantiation.packet] using C.height j
  upper_cofinal := L.window_upper_cofinal
}

/-- family の q は元の continued-fraction denominator。 -/
@[simp] theorem toApproximationFamily_q
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (j : ℕ) :
    C.toApproximationFamily.q j = L.q j := rfl

/-- family の packet は actual corrected packet。 -/
@[simp] theorem toApproximationFamily_packet
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (j : ℕ) :
    C.toApproximationFamily.packet j = L.packet j := rfl

/-- family の start は外部 instantiation の start。 -/
@[simp] theorem toApproximationFamily_start
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L) :
    C.toApproximationFamily.start = L.start := rfl

end ChristoffelHeightInstantiation

end ExternalArithmetic
end CSTMicro
end Collatz2
