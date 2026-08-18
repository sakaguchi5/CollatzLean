import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RankTopWinding
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersStepRankTransport
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.PositiveCostFerrersPotential

/-!
# Local rank-top ledger

bounded positive cell `0 < C < G` に対し、top representative の doubling wrap を
ordinary integer で記録する。

  lambda(G,C) = floor(6C/G) - floor(3C/G).

`0<C<G` では `lambda <= 3`、従って `lambda in {0,1,2,3}`。
また

  (3C mod G) - (6C mod G) = -3C + G*lambda.

normalized local cocycle

  Delta Q = G*carryIndicator - C

と合わせると、rank-top numerator `S-3Q` の jump は

  G * (lambda - 3*carryIndicator)

になる。従って numerator を G で割った winding index J では

  Delta J = lambda - 3*carryIndicator.
-/

namespace Collatz2
namespace CSTMicro

/-- `3C` と `6C` の quotient 差。 -/
def rankTopLambda (G C : ℕ) : ℕ :=
  (6 * C) / G - (3 * C) / G

/-- upper top representative `3C mod G`。 -/
def rankTopResidue3 (G C : ℕ) : ℕ :=
  (3 * C) % G

/-- lower top representative `6C mod G`。 -/
def rankTopResidue6 (G C : ℕ) : ℕ :=
  (6 * C) % G

/-- doubling により quotient は減らない。 -/
theorem three_mul_div_le_six_mul_div
    {G C : ℕ} :
    (3 * C) / G ≤ (6 * C) / G := by
  apply Nat.div_le_div_right
  omega

/-- `0<C<G` では local rank-top quotient jump は最大3。 -/
theorem rankTopLambda_le_three
    {G C : ℕ}
    (hG : 0 < G)
    (hC : C < G) :
    rankTopLambda G C ≤ 3 := by
  let q := (3 * C) / G
  let r := (3 * C) % G
  let q6 := (6 * C) / G
  have hqLt : q < 3 := by
    apply (Nat.div_lt_iff_lt_mul hG).2
    omega
  have hrLt : r < G := by
    dsimp [r]
    exact Nat.mod_lt _ hG
  have hDiv3 := Nat.mod_add_div (3 * C) G
  have hSix : 6 * C = 2 * r + G * (2 * q) := by
    dsimp [q, r] at hDiv3 ⊢
    nlinarith
  have hSixLt : 6 * C < (2 * q + 2) * G := by
    rw [hSix]
    nlinarith
  have hq6Lt : q6 < 2 * q + 2 := by
    apply (Nat.div_lt_iff_lt_mul hG).2
    simpa [q6, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hSixLt
  have hqLe : q ≤ q6 := by
    dsimp [q, q6]
    exact three_mul_div_le_six_mul_div
  unfold rankTopLambda
  dsimp [q, q6] at hqLt hq6Lt hqLe ⊢
  omega

/-- finite alphabet form `lambda in {0,1,2,3}`。 -/
theorem rankTopLambda_cases
    {G C : ℕ}
    (hG : 0 < G)
    (hC : C < G) :
    rankTopLambda G C = 0 ∨
      rankTopLambda G C = 1 ∨
      rankTopLambda G C = 2 ∨
      rankTopLambda G C = 3 := by
  have h := rankTopLambda_le_three hG hC
  omega

/--
ordinary representatives の local exact jump。

  (3C mod G) - (6C mod G) = -3C + G*lambda.
-/
theorem rankTopResidue3_sub_rankTopResidue6
    {G C : ℕ} :
    (rankTopResidue3 G C : ℤ) - (rankTopResidue6 G C : ℤ) =
      -(3 * (C : ℤ)) +
        (G : ℤ) * (rankTopLambda G C : ℤ) := by
  have hqLe : (3 * C) / G ≤ (6 * C) / G :=
    three_mul_div_le_six_mul_div
  have h3 := Nat.mod_add_div (3 * C) G
  have h6 := Nat.mod_add_div (6 * C) G
  have h3z :
      (rankTopResidue3 G C : ℤ) +
          (G : ℤ) * (((3 * C) / G : ℕ) : ℤ) =
        3 * (C : ℤ) := by
    unfold rankTopResidue3
    exact_mod_cast h3
  have h6z :
      (rankTopResidue6 G C : ℤ) +
          (G : ℤ) * (((6 * C) / G : ℕ) : ℤ) =
        6 * (C : ℤ) := by
    unfold rankTopResidue6
    exact_mod_cast h6
  have hLam :
      (rankTopLambda G C : ℤ) =
        (((6 * C) / G : ℕ) : ℤ) -
          (((3 * C) / G : ℕ) : ℤ) := by
    unfold rankTopLambda
    rw [Nat.cast_sub hqLe]
  rw [hLam]
  linarith

/-- rank-top winding numerator。 -/
def rankTopLedgerNumerator (topSum q : ℤ) : ℤ :=
  topSum - 3 * q

/--
pure arithmetic local ledger。
`topUpper-topLower = -3C + G*lambda` と
`qUpper-qLower = G*carry-C` から numerator jump を得る。
-/
theorem rankTopLedgerNumerator_local
    {topLower topUpper qLower qUpper G C lam carry : ℤ}
    (hTop :
      topUpper = topLower - 3 * C + G * lam)
    (hQ :
      qUpper = qLower + G * carry - C) :
    rankTopLedgerNumerator topUpper qUpper =
      rankTopLedgerNumerator topLower qLower +
        G * (lam - 3 * carry) := by
  unfold rankTopLedgerNumerator
  rw [hTop, hQ]
  ring

/-- numerator が双方で G の倍数なら quotient winding J の jump は有限状態になる。 -/
theorem rankTopWindingIndex_local
    {topLower topUpper qLower qUpper G C lam carry JLower JUpper : ℤ}
    (hG : G ≠ 0)
    (hTop :
      topUpper = topLower - 3 * C + G * lam)
    (hQ :
      qUpper = qLower + G * carry - C)
    (hJLower :
      rankTopLedgerNumerator topLower qLower = G * JLower)
    (hJUpper :
      rankTopLedgerNumerator topUpper qUpper = G * JUpper) :
    JUpper - JLower = lam - 3 * carry := by
  have hNum := rankTopLedgerNumerator_local hTop hQ
  rw [hJLower, hJUpper] at hNum
  have hMul :
      G * (JUpper - JLower) = G * (lam - 3 * carry) := by
    linarith
  exact mul_left_cancel₀ hG hMul

namespace FerrersStep

/-- positive residue cell では first-passage cost は ordinary `0<C<G` に入る。 -/
theorem fareyCellCost_toNat_bounded
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hResiduePos : 0 < S.edge.toFareyCellPacket.residue) :
    let G := wordTerminalGap lower
    let C := S.edge.fareyCellCost.toNat
    0 < C ∧ C < G := by
  let G := wordTerminalGap lower
  let C := S.edge.fareyCellCost.toNat
  have hEdgeFP : IsFirstPassageWord S.edge.lowerWord :=
    S.edge_lower_firstPassage hLowerFP
  have hContract : 3 ^ S.edge.oddTotal < S.edge.modulus := by
    have h := hEdgeFP.2.2
    unfold CoefficientContracting at h
    simpa [AdjacentFerrersSwap.modulus] using h
  have hCostPos : 0 < S.edge.fareyCellCost :=
    S.edge.fareyCellCost_pos_of_contracting hContract
  have hCostLt :
      S.edge.fareyCellCost < S.edge.toFareyCellPacket.G :=
    S.edge.fareyCellCost_lt_gap_of_residue_pos hResiduePos
  have hGapEq :=
    S.edge.fareyPacket_G_eq_wordTerminalGap hEdgeFP.2.2
  have hLowerEq : wordTerminalGap S.edge.lowerWord = G := by
    dsimp [G]
    rw [← S.lower_eq]
  have hGInt :
      S.edge.toFareyCellPacket.G = (G : ℤ) := by
    calc
      S.edge.toFareyCellPacket.G
          = (wordTerminalGap S.edge.lowerWord : ℤ) := hGapEq
      _ = (G : ℤ) := by exact_mod_cast hLowerEq
  have hCcast :
      (C : ℤ) = S.edge.fareyCellCost := by
    dsimp [C]
    rw [Int.toNat_of_nonneg (le_of_lt hCostPos)]
  constructor
  · have : (0 : ℤ) < (C : ℤ) := by rw [hCcast]; exact hCostPos
    exact_mod_cast this
  · have : (C : ℤ) < (G : ℤ) := by
      rw [hCcast, ← hGInt]
      exact hCostLt
    exact_mod_cast this

/-- positive-residue first-passage cell の lambda は `0,1,2,3` のいずれか。 -/
theorem rankTopLambda_cell_cases
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hResiduePos : 0 < S.edge.toFareyCellPacket.residue) :
    let G := wordTerminalGap lower
    let C := S.edge.fareyCellCost.toNat
    rankTopLambda G C = 0 ∨
      rankTopLambda G C = 1 ∨
      rankTopLambda G C = 2 ∨
      rankTopLambda G C = 3 := by
  let G := wordTerminalGap lower
  let C := S.edge.fareyCellCost.toNat
  have hBounds := S.fareyCellCost_toNat_bounded hLowerFP hResiduePos
  have hG : 0 < G := lt_trans hBounds.1 hBounds.2
  exact rankTopLambda_cases hG hBounds.2

end FerrersStep

end CSTMicro
end Collatz2
