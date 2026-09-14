import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumNoTripleRise

/-!
# Collatz3 CSTConditional: CST 下の flat block 構造

Global CST により next-future-minimum block の positive excess は消える。
従って defect-flat block は whole `(carry, excess)=(0,0)`、すなわち `C` に固定される。

非自明長 `r>1` では先頭 future-minimum exponent が `1` なので、
proper suffix の critical lower bound と whole depth `B_r` を比較すると

* `B_r = B_(r-1) + 2`,
* suffix excess `=1`,

が exact に従う。

suffix carry まで `1` とするには一般 flat だけでは足りない。
本来の double-rise 後の局面では既存 theorem
`δ_(k+1)=δ_k` があるため、flat `δ_l=δ_k` と suffix balance を合わせて
suffix `(carry,excess)=(1,1)` まで exact に閉じる。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST 下の非自明 next-future-minimum block は、
whole excess `0` の内部で suffix excess `1` と最後の Beatty jump `2` を持つ。
-/
theorem nextFutureMinimum_nontrivial_jumpTwo_suffixExcessOne_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hLong : i + 1 < j) :
    Critical.beattyIndex (j - i) =
        Critical.beattyIndex (j - i - 1) + 2 ∧
      O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1 := by
  let r : ℕ := j - i
  have hrGt : 1 < r := by
    dsimp [r]
    omega
  have hZero : O.segmentBeattyExcess i r = 0 := by
    simpa [r] using
      O.segmentBeattyExcess_eq_zero_of_futureMinimum
        (r := j - i) G hStart
  have hDepthEq :
      Word.twoSteps (O.segmentWord i r) = Critical.beattyIndex r := by
    have hDepth :=
      O.nextFutureMinimum_beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
        hNext
    rw [show j - i = r by rfl, hZero] at hDepth
    omega
  have heI : O.exponent i = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hStart
  have hSuffix :=
    O.nextFutureMinimum_properSuffix_criticalTwoDepth_le
      S hNext (k := i + 1) (by omega) hLong
  have hSuffixLen : j - (i + 1) = r - 1 := by
    dsimp [r]
    omega
  rw [hSuffixLen] at hSuffix
  unfold Critical.criticalTwoDepth at hSuffix
  have hrDecomp : r = (r - 1) + 1 := by omega
  have hTotal :
      Word.twoSteps (O.segmentWord i r) =
        O.exponent i +
          Word.twoSteps (O.segmentWord (i + 1) (r - 1)) := by
    rw [hrDecomp, O.segmentWord_succ]
    simp
  have hLower :
      Critical.beattyIndex (r - 1) + 2 ≤ Critical.beattyIndex r := by
    omega
  have hUpperRaw := beattyIndex_succ_le_add_two (r - 1)
  have hUpper :
      Critical.beattyIndex r ≤ Critical.beattyIndex (r - 1) + 2 := by
    rw [show r - 1 + 1 = r by omega] at hUpperRaw
    exact hUpperRaw
  have hJump :
      Critical.beattyIndex r = Critical.beattyIndex (r - 1) + 2 :=
    Nat.le_antisymm hUpper hLower
  have hSuffixDepth :
      Word.twoSteps (O.segmentWord (i + 1) (r - 1)) =
        Critical.beattyIndex (r - 1) + 1 := by
    omega
  have hSuffixExcess :
      O.segmentBeattyExcess (i + 1) (r - 1) = 1 := by
    unfold segmentBeattyExcess
    rw [hSuffixDepth]
    omega
  constructor
  · simpa [r] using hJump
  · simpa [r, hSuffixLen] using hSuffixExcess

/--
非自明 flat に加えて最初の一歩でも defect が flat なら、proper suffix は exact `(1,1)`。

これは double-rise 直後に使う局所 wrapper。
-/
theorem nextFutureMinimum_nontrivial_flat_suffix_one_one_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hFlat :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i)
    (hFirstStepFlat :
      infiniteSurvivorDefect O.exponent (i + 1) =
        infiniteSurvivorDefect O.exponent i)
    (hLong : i + 1 < j) :
    Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 ∧
      O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1 ∧
      Critical.beattyIndex (j - i) =
        Critical.beattyIndex (j - i - 1) + 2 := by
  have hStructure :=
    O.nextFutureMinimum_nontrivial_jumpTwo_suffixExcessOne_of_globalCST
      G S hStart hNext hLong
  have hBalance :=
    O.nextFutureMinimum_properSuffix_defect_balance
      S hNext (k := i + 1) (by omega) hLong
  have hExcess := hStructure.2
  rw [hExcess, hFlat, hFirstStepFlat] at hBalance
  have hCarry :
      Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 := by
    omega
  exact ⟨hCarry, hExcess, hStructure.1⟩

/--
本丸の specialized form。

二つの `+1` next-future-minimum block `i→j→k` の直後に flat `k→l` が来て、
その flat が非自明 (`k+1<l`) なら、Global CST 下では

* whole `k→l` は `C=(0,0)`,
* proper suffix `k+1→l` は exact `(1,1)`,
* whole length の最後の Beatty jump は exact `2`,

となる。
-/
theorem doubleRise_nextFlat_nontrivial_suffix_one_one_and_jumpTwo_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k l : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hKL : O.NextFutureMinimum k l)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1)
    (hFlatKL :
      infiniteSurvivorDefect O.exponent l =
        infiniteSurvivorDefect O.exponent k)
    (hLong : k + 1 < l) :
    O.transitionSymbol k l = .C ∧
      Critical.beattyCarry (k + 1) (l - (k + 1)) = 1 ∧
      O.segmentBeattyExcess (k + 1) (l - (k + 1)) = 1 ∧
      Critical.beattyIndex (l - k) =
        Critical.beattyIndex (l - k - 1) + 2 := by
  have hMinK : O.FutureMinimumAt k := hJK.futureMinimumAt
  have hWholeC : O.transitionSymbol k l = .C :=
    (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
      G S hMinK hKL).1 hFlatKL
  have hFirstStepFlat :
      infiniteSurvivorDefect O.exponent (k + 1) =
        infiniteSurvivorDefect O.exponent k :=
    O.double_nextFutureMinimum_defect_succ_next_defect_eq
      S hStart hIJ hJK hRiseIJ hRiseJK
  have hSuffix :=
    O.nextFutureMinimum_nontrivial_flat_suffix_one_one_of_globalCST
      G S hMinK hKL hFlatKL hFirstStepFlat hLong
  exact ⟨hWholeC, hSuffix.1, hSuffix.2.1, hSuffix.2.2⟩

end OddOrbit
end Collatz3
