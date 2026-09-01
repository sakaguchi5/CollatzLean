import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorNormalizedCutTerm
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.UniversalCutWeight

/-!
# Pure B exposed predecessor: universal cut weight と `deltaB`

actual minimal bad word の odd-only exponent word を `w`、odd depth を `m` とする。

universal cut weight は

  3^m * W_k = normalizedCutTerm(w,k)          (mod terminalGap w)

を満たし、exposed predecessor では前段から

  normalizedCutTerm(w,k) = 3 * deltaB

である。terminal gap は 3 と coprime なので 3 は unit であり、exposed cut が
proper であることから `m > 0` を使って一個の 3 を cancel すると

  3^(m-1) * W_k = deltaB                     (mod terminalGap w)

を得る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/-- actual minimal bad word の odd-only encoding は FirstCrossing。 -/
theorem actualExponentWord_firstCrossing
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    Collatz2.Word.FirstCrossing (exponentWordOfParity M.word) := by
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  exact
    M.word_firstPassage.exponentWordOfParity_firstCrossing hLen

/--
actual exposed predecessor の universal cut weight を `3^(m-1)` 倍すると、
その Ferrers cell の affine weight `deltaB` に exact 一致する。
-/
theorem exposedPredecessor_universalCutWeight_scaled_eq_deltaB
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hRank : S.edge.rankCut = k) :
    let w := exponentWordOfParity M.word
    let P := M.toPureBProfileObstruction hL
    let hF := M.actualExponentWord_firstCrossing hL
    (((3 ^ (P.m - 1) : ℕ)) : ZMod (Collatz2.Word.terminalGap w)) *
        Collatz2.Word.universalCutWeight hF k =
      ((S.edge.deltaB : ℕ) : ZMod (Collatz2.Word.terminalGap w)) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  let G := Collatz2.Word.terminalGap w
  let hF : Collatz2.Word.FirstCrossing w :=
    M.actualExponentWord_firstCrossing hL
  have hk : k < P.m := by
    simpa [P] using E.lt_m
  have hmPos : 0 < P.m := by
    omega
  have hm : Collatz2.Word.oddSteps w = P.m := by
    rw [oddSteps_exponentWordOfParity]
    symm
    simpa [P, w] using
      M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hTerm :
      Collatz2.Word.normalizedCutTerm w k = 3 * S.edge.deltaB := by
    simpa [w] using
      M.exposedPredecessor_normalizedCutTerm_eq_three_mul_deltaB
        hL E S hRank
  have hUniversal := hF.threePow_mul_universalCutWeight k
  have hScaled :
      (((3 ^ P.m : ℕ)) : ZMod G) *
          Collatz2.Word.universalCutWeight hF k =
        (3 : ZMod G) * ((S.edge.deltaB : ℕ) : ZMod G) := by
    calc
      (((3 ^ P.m : ℕ)) : ZMod G) *
            Collatz2.Word.universalCutWeight hF k
          =
        (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
            Collatz2.Word.universalCutWeight hF k := by
              rw [hm]
      _ = ((Collatz2.Word.normalizedCutTerm w k : ℕ) : ZMod G) := by
            simpa [G] using hUniversal
      _ = (((3 * S.edge.deltaB : ℕ)) : ZMod G) := by
            exact congrArg (fun n : ℕ => (n : ZMod G)) hTerm
      _ = (3 : ZMod G) * ((S.edge.deltaB : ℕ) : ZMod G) := by
            push_cast
            ring
  have hmSplit : P.m = (P.m - 1) + 1 := by
    omega
  have hThreeEq :
      (3 : ZMod G) *
          ((((3 ^ (P.m - 1) : ℕ)) : ZMod G) *
            Collatz2.Word.universalCutWeight hF k) =
        (3 : ZMod G) * ((S.edge.deltaB : ℕ) : ZMod G) := by
    calc
      (3 : ZMod G) *
            ((((3 ^ (P.m - 1) : ℕ)) : ZMod G) *
              Collatz2.Word.universalCutWeight hF k)
          =
        (((3 ^ P.m : ℕ)) : ZMod G) *
            Collatz2.Word.universalCutWeight hF k := by
              rw [hmSplit, pow_succ]
              push_cast
              ring
      _ = (3 : ZMod G) * ((S.edge.deltaB : ℕ) : ZMod G) := hScaled
  let U : (ZMod G)ˣ := hF.terminalThreeUnit
  have hU : (↑U : ZMod G) = 3 := by
    dsimp [U, G]
    simp
  have hUnitEq :
      (↑U : ZMod G) *
          ((((3 ^ (P.m - 1) : ℕ)) : ZMod G) *
            Collatz2.Word.universalCutWeight hF k) =
        (↑U : ZMod G) * ((S.edge.deltaB : ℕ) : ZMod G) := by
    simpa [hU] using hThreeEq
  have hCancel :=
    congrArg
      (fun z : ZMod G => (↑(U⁻¹) : ZMod G) * z)
      hUnitEq
  have hResult :
      (((3 ^ (P.m - 1) : ℕ)) : ZMod G) *
          Collatz2.Word.universalCutWeight hF k =
        ((S.edge.deltaB : ℕ) : ZMod G) := by
    simpa [← mul_assoc] using hCancel
  simpa [P, w, G, hF] using hResult

end MinimalActualABObstructionPacket
end ExternalArithmetic
end CSTMicro
end Collatz2
