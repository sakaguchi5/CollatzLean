import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTopCellActualPredecessor

/-!
# Pure B: terminal top cell に minimal-B geometry を集中

前段で actual terminal top cell predecessor の存在と exact coordinates を得た。
その同じ edge に既存 minimality theorem を適用し、

  HasCarry,
  0 < residue < G,
  q < residue,
  R_B < deltaR

を一 packet に集約する。
さらに既存 terminal-top dictionary により

  deltaB = 2^position * 3^(m-c)

も同じ edge 上で保持する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/-- actual terminal top cell と minimality inequalities を一体化した packet。 -/
structure TerminalTopCellMinimalityPacket
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) where
  lower : ParityWord
  step : FerrersStep lower M.word
  lower_firstPassage : IsFirstPassageWord lower

  position_eq :
    step.edge.position =
      (M.toPureBProfileObstruction hL).terminalTopCellPosition
  fareyLeftExponent_eq :
    step.edge.fareyLeftExponent =
      (M.toPureBProfileObstruction hL).terminalCriticalStart
  oddTotal_eq :
    step.edge.oddTotal =
      (M.toPureBProfileObstruction hL).m

  deltaB_eq_profileTopCellWeight :
    step.edge.deltaB =
      (M.toPureBProfileObstruction hL).terminalTopCellGlobalWeight

  hasCarry : step.edge.HasCarry
  residue_pos : 0 < step.edge.toFareyCellPacket.residue
  residue_lt_gap :
    step.edge.toFareyCellPacket.residue <
      step.edge.toFareyCellPacket.G
  q_lt_residue :
    ((M.toPureBProfileObstruction hL).q : ℤ) <
      step.edge.toFareyCellPacket.residue
  R_lt_deltaR :
    leastRepresentative M.word < step.edge.deltaR

/--
actual minimal B から terminal-top minimality packet を canonical に選ぶ。
-/
noncomputable def terminalTopCellMinimalityPacket
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    TerminalTopCellMinimalityPacket M hL := by
  have hExists :=
    M.exists_terminalTopCellActualPredecessor R hL
  let lower : ParityWord :=
    Classical.choose hExists
  have hLowerExists :
      ∃ S : FerrersStep lower M.word,
        IsFirstPassageWord lower ∧
        S.edge.position =
          (M.toPureBProfileObstruction hL).terminalTopCellPosition ∧
        S.edge.fareyLeftExponent =
          (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
        S.edge.oddTotal =
          (M.toPureBProfileObstruction hL).m := by
    exact Classical.choose_spec hExists
  let S : FerrersStep lower M.word :=
    Classical.choose hLowerExists
  have hData :
      IsFirstPassageWord lower ∧
      S.edge.position =
        (M.toPureBProfileObstruction hL).terminalTopCellPosition ∧
      S.edge.fareyLeftExponent =
        (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
      S.edge.oddTotal =
        (M.toPureBProfileObstruction hL).m := by
    exact Classical.choose_spec hLowerExists
  have hLowerFP :
      IsFirstPassageWord lower :=
    hData.1
  have hPos :
      S.edge.position =
        (M.toPureBProfileObstruction hL).terminalTopCellPosition :=
    hData.2.1
  have hLeft :
      S.edge.fareyLeftExponent =
        (M.toPureBProfileObstruction hL).terminalCriticalStart :=
    hData.2.2.1
  have hOdd :
      S.edge.oddTotal =
        (M.toPureBProfileObstruction hL).m :=
    hData.2.2.2
  have hDelta :
      S.edge.deltaB =
        (M.toPureBProfileObstruction hL).terminalTopCellGlobalWeight :=
    M.terminalTopCell_deltaB_eq_profileTopCellWeight_of_step
      hL S hPos hLeft hOdd
  have hGeom :=
    M.predecessor_geometry_packet S hLowerFP
  refine {
    lower := lower
    step := S
    lower_firstPassage := hLowerFP
    position_eq := hPos
    fareyLeftExponent_eq := hLeft
    oddTotal_eq := hOdd
    deltaB_eq_profileTopCellWeight := hDelta
    hasCarry := hGeom.1
    residue_pos := hGeom.2.1
    residue_lt_gap := hGeom.2.2.1
    q_lt_residue := ?_
    R_lt_deltaR := hGeom.2.2.2.2
  }
  rw [M.toPureBProfileObstruction_q_eq hL]
  exact hGeom.2.2.2.1

/-- terminal top cell そのものに `q < residue` が成立する direct wrapper。 -/
theorem terminalTopCell_q_lt_residue
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let T := M.terminalTopCellMinimalityPacket R hL
    ((M.toPureBProfileObstruction hL).q : ℤ) <
      T.step.edge.toFareyCellPacket.residue := by
  dsimp
  exact (M.terminalTopCellMinimalityPacket R hL).q_lt_residue

/-- terminal top cell そのものに representative carry clearance が成立する。 -/
theorem terminalTopCell_R_lt_deltaR
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let T := M.terminalTopCellMinimalityPacket R hL
    leastRepresentative M.word < T.step.edge.deltaR := by
  dsimp
  exact (M.terminalTopCellMinimalityPacket R hL).R_lt_deltaR

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
