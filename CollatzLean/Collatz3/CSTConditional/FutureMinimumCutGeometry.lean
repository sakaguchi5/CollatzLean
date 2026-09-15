import CollatzLean.Collatz3.CSTConditional.FutureMinimumDefectExact
import CollatzLean.Collatz3.CSTConditional.FutureMinimumRoofCarryCocycle
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimum

/-!
# Collatz3 CSTConditional: next future minimum block の任意 cut 幾何

next-future-minimum block `i -> j` の内部 cut `i+a` を一つ取る。
Global CST により開始点 `i` から cut までの actual two-depth は local Beatty roof 以下、
一方 survivor next-future-minimum 幾何により cut から終点 `j` までの proper tail は
critical roof を strict に越える。

この二方向の情報を total-depth の exact equalityで結ぶと

`tailExcess = localRoofDefect(i,a) + beattyCarry(a, tailLength)`

が得られる。

ここで右辺の carry は absolute index `i+a` の carry ではなく、
block 長を `a + tailLength` と分割した **relative Beatty carry** である。
両者を混同しないため theorem 名にも `relativeCarry` を明記する。

新しい cut state は定義しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
next-future-minimum block の任意 proper internal cut に対する exact law。

`tailExcess = localRoofDefect + relativeCarry`。
-/
theorem nextFutureMinimum_cutTailExcess_eq_localRoofDefect_add_relativeCarry_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j cut : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hCutPos : 0 < cut)
    (hCutInternal : i + cut < j) :
    O.segmentBeattyExcess (i + cut) (j - (i + cut)) =
      O.futureMinimum_localRoofDefect i cut +
        Critical.beattyCarry cut (j - (i + cut)) := by
  let tailLength : ℕ := j - (i + cut)
  have hTailPos : 0 < tailLength := by
    dsimp [tailLength]
    omega
  have hLengthSplit : cut + tailLength = j - i := by
    dsimp [tailLength]
    omega
  have hWhole :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  have hWhole' :
      Word.twoSteps (O.segmentWord i (cut + tailLength)) =
        Critical.beattyIndex (cut + tailLength) := by
    simpa [hLengthSplit] using hWhole
  have hSegment := O.segmentTwoSteps_add_eq i cut tailLength
  have hLocal :=
    O.segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
      G hStart cut
  have hBeatty := Critical.beattyIndex_add_eq cut tailLength
  have hTailCritical :=
    O.nextFutureMinimum_properSuffix_criticalTwoDepth_le
      SInf hNext (k := i + cut) (by omega) hCutInternal
  have hTailCritical' :
      Critical.criticalTwoDepth tailLength ≤
        Word.twoSteps (O.segmentWord (i + cut) tailLength) := by
    simpa [tailLength] using hTailCritical
  have hTailRoof :
      Critical.beattyIndex tailLength ≤
        Word.twoSteps (O.segmentWord (i + cut) tailLength) := by
    unfold Critical.criticalTwoDepth at hTailCritical'
    omega
  unfold segmentBeattyExcess
  dsimp [tailLength] at hWhole' hSegment hBeatty hTailRoof ⊢
  omega

/--
内部 cut が fixed-anchor local roof に接しているなら、proper tail は
relative carry `1` かつ Beatty excess `1` に固定される。
-/
theorem nextFutureMinimum_cutRoofContact_forces_relativeCarry_one_tailExcess_one
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j cut : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hCutPos : 0 < cut)
    (hCutInternal : i + cut < j)
    (hContact : O.futureMinimum_localRoofDefect i cut = 0) :
    Critical.beattyCarry cut (j - (i + cut)) = 1 ∧
      O.segmentBeattyExcess (i + cut) (j - (i + cut)) = 1 := by
  have hLaw :=
    O.nextFutureMinimum_cutTailExcess_eq_localRoofDefect_add_relativeCarry_of_globalCST
      G SInf hStart hNext hCutPos hCutInternal
  have hTailPos :=
    O.nextFutureMinimum_properSuffix_segmentBeattyExcess_pos
      SInf hNext (k := i + cut) (by omega) hCutInternal
  have hCarry := Critical.beattyCarry_le_one cut (j - (i + cut))
  omega

/--
relative carry が `0` の internal cut は fixed-anchor local roof に接触できない。
その cut の local roof defect は strict に正。
-/
theorem nextFutureMinimum_cutLocalRoofDefect_pos_of_relativeCarry_zero
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j cut : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hCutPos : 0 < cut)
    (hCutInternal : i + cut < j)
    (hCarryZero : Critical.beattyCarry cut (j - (i + cut)) = 0) :
    0 < O.futureMinimum_localRoofDefect i cut := by
  have hLaw :=
    O.nextFutureMinimum_cutTailExcess_eq_localRoofDefect_add_relativeCarry_of_globalCST
      G SInf hStart hNext hCutPos hCutInternal
  have hTailPos :=
    O.nextFutureMinimum_properSuffix_segmentBeattyExcess_pos
      SInf hNext (k := i + cut) (by omega) hCutInternal
  omega

end OddOrbit
end Collatz3
