import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.DiagonalSlackCollision
import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog

/-!
# Collatz3 Bridge: RecordFerrers collision 算術の Collatz 特殊化

Experimental2 側では任意 unit-carry roof / 無理回転について、

* rank drop の gcd modulus,
* canonical boundary collision の Diophantine equation,
* collision level に比例する Young 面積余剰

までを一般論として得た。

本ファイルでは Collatz の canonical Beatty roof

`beattyIndex(n) = floor(n log₂ 3)`

へ特殊化する。
整数 slope `1` を正規化した回転角

`θ = log₂(3/2)`

を使うと rank drop は

`m floor(r θ) - r floor(m θ) + m - r`

となる。従って canonical collision は、左側の canonical width prefix と
terminal 側の `θ`-floor rank-drop suffix の exact 整数等式として読める。
-/

namespace Collatz3
namespace Bridge

open Experimental2
open Experimental2.GenericRecordFerrers

/--
Collatz Beatty roof の rank drop を正規化角 `log₂(3/2)` の floor だけで書く。
`beattyIndex` の整数 slope `1` 成分は normalization により完全に消える。
-/
theorem rankDropInt_beattyIndex_eq_floor_logb_three_halves
    (m r : ℕ) :
    GenericRecordFerrers.rankDropInt Critical.beattyIndex m r =
      (m : ℤ) *
          (⌊(r : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ : ℤ) -
        (r : ℤ) *
          (⌊(m : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ : ℤ) +
        (m : ℤ) - (r : ℤ) := by
  rw [GenericRecordFerrers.rankDropInt_eq_normalizedRoofFormula
    beattyIndex_hasUnitCarry]
  rw [normalizeBeatty_eq_natFloor_logb_three_halves r]
  rw [normalizeBeatty_eq_natFloor_logb_three_halves m]

/--
未正規化 slope `log₂ 3` で書いた同値な floor 公式。
こちらは `beattyIndex_eq_natFloor_logb_two_three` を直接代入した形。
-/
theorem rankDropInt_beattyIndex_eq_floor_logb_two_three
    (m r : ℕ) :
    GenericRecordFerrers.rankDropInt Critical.beattyIndex m r =
      (m : ℤ) *
          (⌊(r : ℝ) * Real.logb 2 3⌋₊ : ℤ) -
        (r : ℤ) *
          (⌊(m : ℝ) * Real.logb 2 3⌋₊ : ℤ) +
        (m : ℤ) - (r : ℤ) := by
  rw [GenericRecordFerrers.rankDropInt_eq_roofFormula]
  rw [beattyIndex_eq_natFloor_logb_two_three r]
  rw [beattyIndex_eq_natFloor_logb_two_three m]

/-- Collatz 正規化角 `log₂(3/2)` だけで書いた一 block summand。 -/
noncomputable def collatzRankDropSummand
    (m r : ℕ) : ℤ :=
  (m : ℤ) *
      (⌊(r : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ : ℤ) -
    (r : ℤ) *
      (⌊(m : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ : ℤ) +
    (m : ℤ) - (r : ℤ)

/-- Collatz summand は Beatty rank drop と exact に一致する。 -/
theorem collatzRankDropSummand_eq_rankDropInt
    (m r : ℕ) :
    collatzRankDropSummand m r =
      GenericRecordFerrers.rankDropInt Critical.beattyIndex m r := by
  exact (rankDropInt_beattyIndex_eq_floor_logb_three_halves m r).symm

/-- Collatz rank-drop list sum は正規化角 summand の和。 -/
theorem rankDropIntSum_beattyIndex_eq_sum_collatzSummand
    (m : ℕ) :
    ∀ rs : List ℕ,
      GenericRecordFerrers.rankDropIntSum Critical.beattyIndex m rs =
        (rs.map (collatzRankDropSummand m)).sum
  | [] => by rfl
  | r :: rs => by
      simp only [GenericRecordFerrers.rankDropIntSum, List.map_cons, List.sum_cons]
      rw [← collatzRankDropSummand_eq_rankDropInt m r]
      rw [rankDropIntSum_beattyIndex_eq_sum_collatzSummand m rs]

/--
Collatz の terminal gcd modulus。
canonical collision level は一般 theorem により必ずこの自然数の倍数になる。
-/
def collatzRankDropGcd
    (m : ℕ) : ℕ :=
  GenericRecordFerrers.rankDropGcd Critical.beattyIndex m

/-- Collatz rank-drop gcd は常に正。 -/
theorem collatzRankDropGcd_pos
    (m : ℕ) :
    0 < collatzRankDropGcd m := by
  exact GenericRecordFerrers.rankDropGcd_pos Critical.beattyIndex m

end Bridge

namespace Experimental2
namespace GenericRecordFerrers
namespace RecordFerrers

open Collatz3.Bridge
open YoungFerrersRestricted

/--
Collatz RecordFerrers の rank-drop boundary は、
`θ = log₂(3/2)` の floor summand の和として exact に書ける。
-/
theorem rankDropHeightBoundaryAt_exists_collatzFloorEquation
    {m t : ℕ}
    (R : RecordFerrers Critical.beattyIndex m)
    (hB : R.rankDropHeightBoundaryAt t) :
    ∃ pre suf : List ℕ,
      (canonicalRecordLengths Critical.beattyIndex m R.height).reverse = pre ++ suf ∧
        pre ≠ [] ∧
          (t : ℤ) = (pre.map (collatzRankDropSummand m)).sum := by
  rcases R.rankDropHeightBoundaryAt_exists_rankDropIntSum hB with
    ⟨pre, suf, hSplit, hNonempty, hEq⟩
  refine ⟨pre, suf, hSplit, hNonempty, ?_⟩
  rw [hEq]
  exact rankDropIntSum_beattyIndex_eq_sum_collatzSummand m pre

/--
Collatz canonical collision を、左 prefix width と
`θ = log₂(3/2)` floor summand の terminal-side suffix sum の exact equation として明示する。
-/
theorem hasCanonicalBoundaryCollision_exists_collatzFloorEquation
    {m t : ℕ}
    (R : RecordFerrers Critical.beattyIndex m)
    (hC : R.HasCanonicalBoundaryCollision t) :
    ∃ pre preRest revTail revRest : List ℕ,
      canonicalRecordLengths Critical.beattyIndex m R.height = pre ++ preRest ∧
        pre ≠ [] ∧
        (canonicalRecordLengths Critical.beattyIndex m R.height).reverse =
          revTail ++ revRest ∧
        revTail ≠ [] ∧
        pre.sum = t ∧
        (pre.sum : ℤ) = (revTail.map (collatzRankDropSummand m)).sum := by
  rcases R.canonicalWidthBoundaryAt_exists_prefixSum hC.1 with
    ⟨pre, preRest, hPreSplit, hPreNonempty, hPreSum⟩
  rcases R.rankDropHeightBoundaryAt_exists_collatzFloorEquation hC.2 with
    ⟨revTail, revRest, hRevSplit, hRevNonempty, hEq⟩
  refine ⟨pre, preRest, revTail, revRest,
    hPreSplit, hPreNonempty, hRevSplit, hRevNonempty, hPreSum, ?_⟩
  have hPreSumZ : (pre.sum : ℤ) = (t : ℤ) := by
    exact_mod_cast hPreSum
  rw [hPreSumZ]
  exact hEq

/--
Collatz の internal collision level は `collatzRankDropGcd m` の倍数。
Bridge 側の名前で使いやすい wrapper を公開する。
-/
theorem hasCanonicalBoundaryCollision_collatzRankDropGcd_dvd
    {m t : ℕ}
    (R : RecordFerrers Critical.beattyIndex m)
    (hC : R.HasCanonicalBoundaryCollision t) :
    Collatz3.Bridge.collatzRankDropGcd m ∣ t := by
  exact R.hasCanonicalBoundaryCollision_rankDropGcd_dvd_nat hC

/--
Collatz でも level `t` の internal collision は Young 面積余剰 `>= 2t` を強制する。
-/
theorem two_mul_collisionLevel_le_youngCellCount_sub_basisWeightZ_collatz
    {m t : ℕ}
    (R : RecordFerrers Critical.beattyIndex m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (2 : ℤ) * (t : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  exact R.two_mul_collisionLevel_le_youngCellCount_sub_basisWeightZ ht htD hC

/--
Collatz internal collision は少なくとも `2 * collatzRankDropGcd m` の面積余剰を強制する。
-/
theorem two_mul_collatzRankDropGcd_le_youngCellCount_sub_basisWeightZ_of_internalCollision
    {m t : ℕ}
    (R : RecordFerrers Critical.beattyIndex m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (2 : ℤ) * (Collatz3.Bridge.collatzRankDropGcd m : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  exact
    R.two_mul_rankDropGcd_le_youngCellCount_sub_basisWeightZ_of_internalCollision
      ht htD hC

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
