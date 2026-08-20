import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalDepthTwoCarryModSix

/-!
# Pure B: terminal top cell predecessor on the profile side

`c=terminalCriticalStart`, `c>0` では `h(c-1)>0`。
その右端 top cell を一個だけ除く profile を canonical に定義する。
この操作は terminal core から exact に一個の dyadic top-cell weight を引く。

actual parity/Ferrers word への realization は別 theorem で座標を接続する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- terminal top cell の column。 -/
noncomputable def terminalTopColumn
    (P : PureBProfileObstruction) : ℕ :=
  P.terminalCriticalStart - 1

/-- terminal top cell の dyadic position `β(c-1)-h(c-1)`。 -/
noncomputable def terminalTopCellPosition
    (P : PureBProfileObstruction) : ℕ :=
  beattyIndex P.terminalTopColumn - P.h P.terminalTopColumn

/-- local terminal core scale での top-cell weight。 -/
noncomputable def terminalTopCellLocalWeight
    (P : PureBProfileObstruction) : ℕ :=
  2 ^ P.terminalTopCellPosition

/-- global `m` scale での同じ cell weight。 -/
noncomputable def terminalTopCellGlobalWeight
    (P : PureBProfileObstruction) : ℕ :=
  2 ^ P.terminalTopCellPosition *
    3 ^ (P.m - P.terminalCriticalStart)

/-- terminal top cell を一個だけ除いた profile。 -/
noncomputable def terminalTopCellPredecessor
    (P : PureBProfileObstruction) : ℕ → ℕ :=
  fun k =>
    if k = P.terminalTopColumn then P.h k - 1 else P.h k

/-- predecessor は terminal column で exact に一層下がる。 -/
theorem terminalTopCellPredecessor_at_top
    (P : PureBProfileObstruction) :
    P.terminalTopCellPredecessor P.terminalTopColumn =
      P.h P.terminalTopColumn - 1 := by
  simp [terminalTopCellPredecessor]

/-- top column 以外は不変。 -/
theorem terminalTopCellPredecessor_of_ne
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k ≠ P.terminalTopColumn) :
    P.terminalTopCellPredecessor k = P.h k := by
  simp [terminalTopCellPredecessor, hk]

/-- positive start の actual B situation では top cell は genuine に存在する。 -/
theorem terminalTopCell_exists
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    0 < P.h P.terminalTopColumn := by
  have hcPos : 0 < P.terminalCriticalStart := by
    have hle := P.criticalizationStart_le_terminalCriticalStart
    omega
  simpa [terminalTopColumn] using P.terminalLastDepth_pos hcPos

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
