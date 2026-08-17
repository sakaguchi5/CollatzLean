import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacketClosure
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelHeightBound
import Mathlib.Tactic.Ring

/-!
# Step 6: explicit Christoffel numerator -> uniform height H = 4

`criticalChristoffelPhi` は既に explicit finite fold になっている。
ここでは各 Christoffel term が `2^q` 以下という finite balance certificate から

  0 <= phi_j <= q_j * 2^q_j

を導き、odd/even corrected formulas を通して

  |P_j|, |Q_j| <= 4 q_j 2^q_j

を証明する。

外部超越数論は使わない。残る input は finite Christoffel balance だけである。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
explicit Christoffel sum の各項を `2^q_j` で抑えるための finite geometry data。
actual convergent/Christoffel identificationから埋める elementary certificate。
-/
structure CriticalChristoffelHeightGeometry
    (D : OrientedCriticalContinuedFractionData) where
  /-- critical convergent numerator は denominator 以下。 -/
  p_le_q :
    ∀ j : ℕ, D.base.p j ≤ D.base.q j

  /-- explicit `phi_j` の各 summand は `2^q_j` 以下。 -/
  term_le_twoPow :
    ∀ j i : ℕ,
      i < D.base.p j →
      (3 : ℤ) ^ (D.base.p j - 1 - i) *
          (2 : ℤ) ^ ((i * D.base.q j) / D.base.p j) ≤
        (2 : ℤ) ^ D.base.q j

private theorem foldl_add_le_length_mul
    (xs : List ℕ)
    (f : ℕ → ℤ)
    (M a : ℤ)
    (hf : ∀ x : ℕ, x ∈ xs → f x ≤ M) :
    xs.foldl (fun acc x => acc + f x) a ≤
      a + (xs.length : ℤ) * M := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hx : f x ≤ M := hf x (by simp)
      have htail : ∀ y : ℕ, y ∈ xs → f y ≤ M := by
        intro y hy
        exact hf y (by simp [hy])
      have hih := ih (a := a + f x) htail
      calc
        xs.foldl (fun acc y => acc + f y) (a + f x)
            ≤ (a + f x) + (xs.length : ℤ) * M := hih
        _ ≤ (a + M) + (xs.length : ℤ) * M := by
          linarith
        _ = a + ((xs.length + 1 : ℕ) : ℤ) * M := by
          push_cast
          ring

private theorem criticalChristoffelPhi_nonneg
    (p q : ℕ) :
    0 ≤ criticalChristoffelPhi p q := by
  by_cases hp : p = 0
  · simp [criticalChristoffelPhi, hp]
  · exact le_of_lt (criticalChristoffelPhi_pos (Nat.pos_of_ne_zero hp))

namespace CriticalChristoffelHeightGeometry

/-- explicit finite fold から `phi_j <= p_j * 2^q_j`。 -/
theorem phi_le_p_mul_twoPow
    {D : OrientedCriticalContinuedFractionData}
    (G : CriticalChristoffelHeightGeometry D)
    (j : ℕ) :
    criticalChristoffelPhiAt D.base j ≤
      (D.base.p j : ℤ) * (2 : ℤ) ^ D.base.q j := by
  unfold criticalChristoffelPhiAt criticalChristoffelPhi
  let f : ℕ → ℤ := fun i =>
    (3 : ℤ) ^ (D.base.p j - 1 - i) *
      (2 : ℤ) ^ ((i * D.base.q j) / D.base.p j)
  have hf :
      ∀ i : ℕ, i ∈ List.range (D.base.p j) →
        f i ≤ (2 : ℤ) ^ D.base.q j := by
    intro i hi
    have hil : i < D.base.p j := by
      simpa using hi
    simpa [f] using G.term_le_twoPow j i hil
  have hfold :=
    foldl_add_le_length_mul
      (List.range (D.base.p j)) f
      ((2 : ℤ) ^ D.base.q j) 0 hf
  simpa [f] using hfold

/-- `p_j <= q_j` を使って `phi_j <= q_j * 2^q_j`。 -/
theorem phi_le_q_mul_twoPow
    {D : OrientedCriticalContinuedFractionData}
    (G : CriticalChristoffelHeightGeometry D)
    (j : ℕ) :
    criticalChristoffelPhiAt D.base j ≤
      (D.base.q j : ℤ) * (2 : ℤ) ^ D.base.q j := by
  have hphi := G.phi_le_p_mul_twoPow j
  have hpq : (D.base.p j : ℤ) ≤ D.base.q j := by
    exact_mod_cast G.p_le_q j
  have hpow : 0 ≤ (2 : ℤ) ^ D.base.q j := by positivity
  have hmul :
      (D.base.p j : ℤ) * (2 : ℤ) ^ D.base.q j ≤
        (D.base.q j : ℤ) * (2 : ℤ) ^ D.base.q j :=
    mul_le_mul_of_nonneg_right hpq hpow
  exact le_trans hphi hmul

/--
odd index では、explicit corrected Christoffel packet の
numerator / denominator は共通 height
`4 * q_j * 2^q_j`
で抑えられる。
-/
theorem odd_correctedChristoffel_height_bound
    (D : OrientedCriticalContinuedFractionData)
    (G : CriticalChristoffelHeightGeometry D)
    {j : ℕ}
    (hjOdd : j % 2 = 1) :
    HasChristoffelHeightBound
      4
      (D.base.q j)
      (correctedChristoffelP D.base j)
      (correctedChristoffelQ D.base j) := by
  have hqPos : 0 < D.base.q j :=
    D.q_pos_all j
  have hqOneZ : (1 : ℤ) ≤ D.base.q j := by
    exact_mod_cast hqPos
  have htwoPos :
      0 < (2 : ℤ) ^ D.base.q j := by
    positivity
  have hphiNonneg :
      0 ≤ criticalChristoffelPhiAt D.base j := by
    unfold criticalChristoffelPhiAt
    exact
      criticalChristoffelPhi_nonneg
        (D.base.p j)
        (D.base.q j)
  have hphiUpper :=
    G.phi_le_q_mul_twoPow j
  have hterm0 :=
    G.term_le_twoPow j 0 (D.odd_p_pos j hjOdd)
  have hthreePred :
      (3 : ℤ) ^ (D.base.p j - 1) ≤
        (2 : ℤ) ^ D.base.q j := by
    simpa using hterm0
  have hpEq :
      D.base.p j = (D.base.p j - 1) + 1 := by
    have hpPos := D.odd_p_pos j hjOdd
    omega
  have hthree :
      (3 : ℤ) ^ D.base.p j ≤
        3 * (2 : ℤ) ^ D.base.q j := by
    rw [hpEq, pow_succ]
    nlinarith
  have hQpos :
      0 <
        (3 : ℤ) ^ D.base.p j -
          (2 : ℤ) ^ D.base.q j :=
    D.odd_gap_pos hjOdd
  have hMcast :
      (((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ)) =
        4 * (D.base.q j : ℤ) *
          (2 : ℤ) ^ D.base.q j := by
    push_cast
    ring
  change
    ((-(((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ)) ≤
        correctedChristoffelP D.base j ∧
      correctedChristoffelP D.base j ≤
        (((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ))) ∧
    (-(((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ)) ≤
        correctedChristoffelQ D.base j ∧
      correctedChristoffelQ D.base j ≤
        (((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ))))
  rw [correctedChristoffelP_odd D.base hjOdd]
  rw [correctedChristoffelQ_odd D.base hjOdd]
  rw [hMcast]
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith


/--
even index では、explicit corrected Christoffel packet の
numerator / denominator は共通 height
`4 * q_j * 2^q_j`
で抑えられる。
-/
theorem even_correctedChristoffel_height_bound
    (D : OrientedCriticalContinuedFractionData)
    (G : CriticalChristoffelHeightGeometry D)
    {j : ℕ}
    (hjEven : j % 2 = 0) :
    HasChristoffelHeightBound
      4
      (D.base.q j)
      (correctedChristoffelP D.base j)
      (correctedChristoffelQ D.base j) := by
  have hqPos : 0 < D.base.q j :=
    D.q_pos_all j
  have hqOneZ : (1 : ℤ) ≤ D.base.q j := by
    exact_mod_cast hqPos
  have htwoPos :
      0 < (2 : ℤ) ^ D.base.q j := by
    positivity
  have hphiNonneg :
      0 ≤ criticalChristoffelPhiAt D.base j := by
    unfold criticalChristoffelPhiAt
    exact
      criticalChristoffelPhi_nonneg
        (D.base.p j)
        (D.base.q j)
  have hphiUpper :=
    G.phi_le_q_mul_twoPow j
  have hQgap :
      0 <
        (2 : ℤ) ^ D.base.q j -
          (3 : ℤ) ^ D.base.p j :=
    D.even_gap_pos hjEven
  have hthreePos :
      0 < (3 : ℤ) ^ D.base.p j := by
    positivity
  have hTwoPredNat :
      2 ^ (D.base.q j - 1) ≤
        2 ^ D.base.q j :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (by omega)
  have hTwoPred :
      (2 : ℤ) ^ (D.base.q j - 1) ≤
        (2 : ℤ) ^ D.base.q j := by
    exact_mod_cast hTwoPredNat
  have hMcast :
      (((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ)) =
        4 * (D.base.q j : ℤ) *
          (2 : ℤ) ^ D.base.q j := by
    push_cast
    ring
  change
    ((-(((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ)) ≤
        correctedChristoffelP D.base j ∧
      correctedChristoffelP D.base j ≤
        (((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ))) ∧
    (-(((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ)) ≤
        correctedChristoffelQ D.base j ∧
      correctedChristoffelQ D.base j ≤
        (((4 * D.base.q j * 2 ^ D.base.q j : ℕ) : ℤ))))
  rw [correctedChristoffelP_even D.base hjEven]
  rw [correctedChristoffelQ_even D.base hjEven]
  rw [hMcast]
  constructor
  · constructor
    · have hTwoPredNonneg :
          0 ≤ (2 : ℤ) ^ (D.base.q j - 1) := by
        positivity
      have hProdNonneg :
          0 ≤ (D.base.q j : ℤ) *
            (2 : ℤ) ^ D.base.q j := by
        positivity
      calc
        -(4 * (D.base.q j : ℤ) *
              (2 : ℤ) ^ D.base.q j)
            ≤
          -(3 * (D.base.q j : ℤ) *
              (2 : ℤ) ^ D.base.q j) := by
                nlinarith
        _ ≤
          -3 * criticalChristoffelPhiAt D.base j := by
                nlinarith [hphiUpper]
        _ ≤
          (2 : ℤ) ^ (D.base.q j - 1) -
            3 * criticalChristoffelPhiAt D.base j := by
                nlinarith
    · nlinarith
  · constructor <;> nlinarith

/--
odd / even の二枝を統合すると、
explicit corrected Christoffel packet には
全 index で一様な height constant `H = 4` が使える。
-/
theorem correctedChristoffel_height_bound
    (D : OrientedCriticalContinuedFractionData)
    (G : CriticalChristoffelHeightGeometry D)
    (j : ℕ) :
    HasChristoffelHeightBound
      4
      (D.base.q j)
      (correctedChristoffelP D.base j)
      (correctedChristoffelQ D.base j) := by
  have hmod :
      j % 2 < 2 :=
    Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · exact
      odd_correctedChristoffel_height_bound
        D G hjOdd
  · have hjEven : j % 2 = 0 := by
      omega
    exact
      even_correctedChristoffel_height_bound
        D G hjEven


/--
Step 6:
explicit corrected Christoffel packet に対する branchwise height estimate を統合し、
一様定数 `H = 4` を持つ Christoffel height instantiation を構成する。
-/
def toChristoffelHeightInstantiation
    {D : OrientedCriticalContinuedFractionData}
    (G : CriticalChristoffelHeightGeometry D) :
    ChristoffelHeightInstantiation
      D.toCriticalChristoffelPacket.toLopezStollInstantiation := by
  refine {
    H := 4
    height := ?_
  }
  intro j
  change
    HasChristoffelHeightBound
      4
      (D.base.q j)
      (correctedChristoffelP D.base j)
      (correctedChristoffelQ D.base j)
  exact correctedChristoffel_height_bound D G j

@[simp] theorem toChristoffelHeightInstantiation_H
    {D : OrientedCriticalContinuedFractionData}
    (G : CriticalChristoffelHeightGeometry D) :
    G.toChristoffelHeightInstantiation.H = 4 := rfl

end CriticalChristoffelHeightGeometry

end ExternalArithmetic
end CSTMicro
end Collatz2
