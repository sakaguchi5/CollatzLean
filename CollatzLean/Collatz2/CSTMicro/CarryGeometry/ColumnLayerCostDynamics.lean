import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnLayerFareyBridge
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadCellCostObstruction

/-!
# Column/layer cell-cost dynamics

`ColumnLayerFareyBridge` では、critical boundary から測った rank column `k` と
current layer `j` から actual adjacent Ferrers cell の Farey residue / cost を
canonical に復元した。

ここでは cell cost

  C = G - D

に対して Farey determinant の dual identity を使い、

  3^a C = G*q + 2^i

を exact に証明する。actual column/layer 座標では

  a = k+1,
  i = criticalHeight(k)-j-1,

なので、right exponent まで掛けると

  3^m C = G*T + 2^i 3^(m-k-1)

となる。右端の power term は endpoint `(m,k,j)` だけから決まる。

さらに同じ column を一層深くすると `i` が 1 減るため、この power term は
exact inverse-doubling law

  2 * term(k,j+1) = term(k,j)

を満たす。
-/

namespace Collatz2
namespace CSTMicro

/--
column/layer cell が terminal odd exponent `m` へ寄与する canonical scaled power term。

actual cell では `i = columnLayerPosition k j`、`r = m-(k+1)` なので
`2^i * 3^r` そのもの。
-/
def columnLayerScaledPowerTerm
    (m k j : ℕ) : ℤ :=
  (2 : ℤ) ^ columnLayerPosition k j *
    (3 : ℤ) ^ (m - (k + 1))

namespace AdjacentFerrersSwap

/--
Farey residue の complement `C = G-D` に対する dual exact identity。

  3^a * C = G*q + 2^i.

ここで `q` は local inverse equation
`3^a*u = 1 + 2^d*q` の quotient。
-/
theorem threePow_mul_fareyCellCost_eq_gap_mul_localQuotient_add_twoPow
    (S : AdjacentFerrersSwap) :
    (3 : ℤ) ^ S.fareyLeftExponent * S.fareyCellCost =
      S.toFareyCellPacket.G * (S.fareyLocalQuotient : ℤ) +
        (2 : ℤ) ^ S.position := by
  have hResid := S.toFareyCellPacket.threePow_mul_residue
  have hResid' :
      (3 : ℤ) ^ S.fareyLeftExponent *
          S.toFareyCellPacket.residue =
        S.toFareyCellPacket.G * S.fareyS -
          (2 : ℤ) ^ S.position := by
    simpa [AdjacentFerrersSwap.toFareyCellPacket] using hResid
  unfold AdjacentFerrersSwap.fareyCellCost
  calc
    (3 : ℤ) ^ S.fareyLeftExponent *
          (S.toFareyCellPacket.G - S.toFareyCellPacket.residue)
        =
      (3 : ℤ) ^ S.fareyLeftExponent * S.toFareyCellPacket.G -
        (3 : ℤ) ^ S.fareyLeftExponent *
          S.toFareyCellPacket.residue := by ring
    _ =
      (3 : ℤ) ^ S.fareyLeftExponent * S.toFareyCellPacket.G -
        (S.toFareyCellPacket.G * S.fareyS -
          (2 : ℤ) ^ S.position) := by rw [hResid']
    _ =
      S.toFareyCellPacket.G * (S.fareyLocalQuotient : ℤ) +
        (2 : ℤ) ^ S.position := by
          unfold AdjacentFerrersSwap.fareyS
          ring

/--
right exponent `r` まで掛けた full odd-scale identity。

  3^m * C
    = G * (q * 3^r) + 2^i * 3^r.
-/
theorem threePow_oddTotal_mul_fareyCellCost_eq_gap_mul_scaledQuotient_add_scaledTwoPow
    (S : AdjacentFerrersSwap) :
    (3 : ℤ) ^ S.oddTotal * S.fareyCellCost =
      S.toFareyCellPacket.G *
          ((S.fareyLocalQuotient : ℤ) *
            (3 : ℤ) ^ S.fareyRightExponent) +
        (2 : ℤ) ^ S.position *
          (3 : ℤ) ^ S.fareyRightExponent := by
  have hCore :=
    S.threePow_mul_fareyCellCost_eq_gap_mul_localQuotient_add_twoPow
  rw [S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent, pow_add]
  calc
    ((3 : ℤ) ^ S.fareyLeftExponent *
          (3 : ℤ) ^ S.fareyRightExponent) * S.fareyCellCost
        =
      (3 : ℤ) ^ S.fareyRightExponent *
        ((3 : ℤ) ^ S.fareyLeftExponent * S.fareyCellCost) := by ring
    _ =
      (3 : ℤ) ^ S.fareyRightExponent *
        (S.toFareyCellPacket.G * (S.fareyLocalQuotient : ℤ) +
          (2 : ℤ) ^ S.position) := by rw [hCore]
    _ =
      S.toFareyCellPacket.G *
          ((S.fareyLocalQuotient : ℤ) *
            (3 : ℤ) ^ S.fareyRightExponent) +
        (2 : ℤ) ^ S.position *
          (3 : ℤ) ^ S.fareyRightExponent := by ring

/-- Farey right exponent は endpoint odd total から selected rank column を引いたもの。 -/
theorem fareyRightExponent_eq_oddTotal_sub_rankCut_succ
    (S : AdjacentFerrersSwap) :
    S.fareyRightExponent = S.oddTotal - (S.rankCut + 1) := by
  have hOdd := S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent
  have hLeft := S.fareyLeftExponent_eq_rankCut_add_one
  rw [hLeft] at hOdd
  omega

end AdjacentFerrersSwap

namespace FerrersStep

/-- first-passage selected cell では naturalized cost を integer に戻しても元の cost。 -/
theorem fareyCellCost_toNat_cast_eq
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    (S.edge.fareyCellCost.toNat : ℤ) = S.edge.fareyCellCost := by
  have hEdgeLowerFP : IsFirstPassageWord S.edge.lowerWord :=
    S.edge_lower_firstPassage hLowerFP
  have hContract :
      3 ^ S.edge.oddTotal < 2 ^ S.edge.length := by
    have h := hEdgeLowerFP.2.2
    unfold CoefficientContracting at h
    rw [S.edge.lowerWord_oddCount, S.edge.lowerWord_length] at h
    exact h
  have hPos : 0 < S.edge.fareyCellCost :=
    S.edge.fareyCellCost_pos_of_contracting hContract
  exact Int.toNat_of_nonneg (le_of_lt hPos)

/--
actual first-passage cell を canonical `(m,k,j)` power termへ移した exact witness equation。

  3^m * C(k,j) = G*T + columnLayerScaledPowerTerm(m,k,j).

`T` の具体値は local quotient `q * 3^r` だが、後段では existence だけでよい。
-/
theorem columnLayerCellCost_scaled_exact
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    ∃ T : ℤ,
      (3 : ℤ) ^ S.edge.oddTotal *
          (columnLayerCellCostNat
            S.edge.length S.edge.oddTotal S.edge.rankCut j : ℤ) =
        (columnLayerGap S.edge.length S.edge.oddTotal : ℤ) * T +
          columnLayerScaledPowerTerm
            S.edge.oddTotal S.edge.rankCut j := by
  let T : ℤ :=
    (S.edge.fareyLocalQuotient : ℤ) *
      (3 : ℤ) ^ S.edge.fareyRightExponent
  refine ⟨T, ?_⟩
  have hCore :=
    S.edge.threePow_oddTotal_mul_fareyCellCost_eq_gap_mul_scaledQuotient_add_scaledTwoPow
  have hCostNat :=
    S.fareyCellCost_toNat_eq_columnLayerCellCostNat hLowerFP hDepth
  have hCostCast := S.fareyCellCost_toNat_cast_eq hLowerFP
  have hCostColumn :
      (columnLayerCellCostNat
          S.edge.length S.edge.oddTotal S.edge.rankCut j : ℤ) =
        S.edge.fareyCellCost := by
    calc
      (columnLayerCellCostNat
          S.edge.length S.edge.oddTotal S.edge.rankCut j : ℤ)
          = (S.edge.fareyCellCost.toNat : ℤ) := by
              exact_mod_cast hCostNat.symm
      _ = S.edge.fareyCellCost := hCostCast
  have hGap := S.fareyGap_eq_columnLayerGap_cast hLowerFP
  have hPosition :=
    S.position_eq_columnLayerPosition_of_lower_extraDepth hLowerFP hDepth
  have hRight :=
    S.edge.fareyRightExponent_eq_oddTotal_sub_rankCut_succ
  rw [← hCostColumn, hGap, hPosition, hRight] at hCore
  simpa [T, columnLayerScaledPowerTerm, hRight] using hCore

end FerrersStep

/--
一層深い cell が存在する範囲では standard position は exact に 1 減る。
-/
theorem columnLayerPosition_succ
    {k j : ℕ}
    (hInside : j + 1 < Collatz2.Word.criticalHeight k) :
    columnLayerPosition k (j + 1) + 1 =
      columnLayerPosition k j := by
  unfold columnLayerPosition
  omega

/--
同じ column を一層深くすると scaled power term は exact に半分になる。

  2 * term(k,j+1) = term(k,j).
-/
theorem two_mul_columnLayerScaledPowerTerm_succ
    {m k j : ℕ}
    (hInside : j + 1 < Collatz2.Word.criticalHeight k) :
    2 * columnLayerScaledPowerTerm m k (j + 1) =
      columnLayerScaledPowerTerm m k j := by
  have hPos := columnLayerPosition_succ hInside
  unfold columnLayerScaledPowerTerm
  rw [← hPos]
  rw [pow_succ]
  ring

end CSTMicro
end Collatz2
