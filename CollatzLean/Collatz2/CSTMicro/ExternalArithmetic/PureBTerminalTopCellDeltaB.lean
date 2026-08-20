import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTopCellPredecessor
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadPredecessorGeometry

/-!
# Pure B: terminal top cell weight = Ferrers deltaB

actual Ferrers predecessor edge が terminal top cell の座標

  position = β(c-1)-h(c-1),
  fareyLeftExponent = c,
  oddTotal = m

を実現したなら、その adjacent affine change `deltaB` は global profile の
terminal top-cell weight

  2^position * 3^(m-c)

と exact に一致する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- matching terminal-top coordinates を持つ Ferrers cell の deltaB は profile weight。 -/
theorem terminalTopCell_deltaB_eq_profileTopCellWeight
    (P : PureBProfileObstruction)
    (S : AdjacentFerrersSwap)
    (hPos : S.position = P.terminalTopCellPosition)
    (hLeft : S.fareyLeftExponent = P.terminalCriticalStart)
    (hOdd : S.oddTotal = P.m) :
    S.deltaB = P.terminalTopCellGlobalWeight := by
  have hRight :
      oddCount S.rightContext = P.m - P.terminalCriticalStart := by
    unfold AdjacentFerrersSwap.fareyLeftExponent at hLeft
    unfold AdjacentFerrersSwap.oddTotal at hOdd
    omega
  unfold AdjacentFerrersSwap.deltaB terminalTopCellGlobalWeight
  rw [hPos, hRight]

end PureBProfileObstruction

namespace MinimalActualABObstructionPacket

/--
actual predecessor step が terminal-top coordinates を実現した場合の thin wrapper。
この形で minimality の `q < residue`, `R < deltaR` と同じ edge を直接使える。
-/
theorem terminalTopCell_deltaB_eq_profileTopCellWeight_of_step
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hPos :
      S.edge.position =
        (M.toPureBProfileObstruction hL).terminalTopCellPosition)
    (hLeft :
      S.edge.fareyLeftExponent =
        (M.toPureBProfileObstruction hL).terminalCriticalStart)
    (hOdd :
      S.edge.oddTotal =
        (M.toPureBProfileObstruction hL).m) :
    S.edge.deltaB =
      (M.toPureBProfileObstruction hL).terminalTopCellGlobalWeight := by
  exact
    (M.toPureBProfileObstruction hL).terminalTopCell_deltaB_eq_profileTopCellWeight
      S.edge hPos hLeft hOdd

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
