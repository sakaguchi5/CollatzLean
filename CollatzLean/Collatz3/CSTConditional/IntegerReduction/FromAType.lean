import CollatzLean.Collatz3.CSTConditional.IntegerReduction.EventualPeriodicity
import CollatzLean.Collatz3.CSTConditional.FutureMinimumShiftSelfSimilarity
import CollatzLean.Collatz3.CSTConditional.FutureMinimumCutGeometry
import CollatzLean.Collatz3.CSTConditional.ALinearGrowth

/-!
# Collatz3 CSTConditional IntegerReduction: A 型 actual 軌道から純整数系への bridge

このファイルだけが actual `OddOrbit` / `GlobalCST` を import する。
1--12 の純整数層へ向かう一方向 bridge として使う。

primitive package は作らない。
薄い座標として

* future-minimum block length 列、
* chosen future minimum から shift した exponent/value 列

だけを定義し、それ以外は既存 theorem から導く。
-/

namespace Collatz3
namespace IntegerReduction

open Bridge
open CSTConditional

/-- 標準 future-minimum 列を `start` 番目から見た block length。 -/
def futureMinimumLengthFrom
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (start n : ℕ) : ℕ :=
  F.index (start + n + 1) - F.index (start + n)

/-- chosen future minimum から odd-step 時間を 0 に戻した exponent stream。 -/
def futureMinimumShiftedExponent
    (O : Collatz3.OddOrbit)
    (anchor : ℕ) : ℕ → ℕ :=
  fun m => O.exponent (anchor + m)

/-- chosen future minimum から odd-step 時間を 0 に戻した value stream。 -/
def futureMinimumShiftedValue
    (O : Collatz3.OddOrbit)
    (anchor : ℕ) : ℕ → ℕ :=
  fun m => O.value (anchor + m)

/-- future-minimum length の boundary sum は selector index 差そのもの。 -/
theorem boundaryIndex_futureMinimumLengthFrom
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (start n : ℕ) :
    boundaryIndex (futureMinimumLengthFrom F start) n =
      F.index (start + n) - F.index start := by
  induction n with
  | zero => simp [boundaryIndex, futureMinimumLengthFrom]
  | succ n ih =>
      rw [boundaryIndex_succ, ih]
      unfold futureMinimumLengthFrom
      have h0 : F.index start ≤ F.index (start + n) := by
        apply F.index_strict.monotone
        omega
      have h1 : F.index (start + n) ≤ F.index (start + n + 1) := by
        exact Nat.le_of_lt (F.index_strict (by omega))
      have hArg :
          start + (n + 1) = start + n + 1 := by
        omega
      rw [hArg]
      omega

/-- shifted stream の pure segment word は actual segment word と exact に一致。 -/
theorem streamWord_futureMinimumShiftedExponent
    (O : Collatz3.OddOrbit)
    (anchor start r : ℕ) :
    streamWord (futureMinimumShiftedExponent O anchor) start r =
      O.segmentWord (anchor + start) r := by
  induction r with
  | zero => simp [streamWord]
  | succ r ih =>
      rw [streamWord_succ]
      rw [ih]
      have hActual := O.segmentWord_add (anchor + start) r 1
      rw [hActual]
      simp [futureMinimumShiftedExponent, OddOrbit.segmentWord, Nat.add_assoc]

/-- actual odd orbit は shift すると独立 `RunsOddRecurrence` を実現する。 -/
theorem oddRecurrence_futureMinimumShifted
    (O : Collatz3.OddOrbit)
    (anchor : ℕ) :
    RunsOddRecurrence
      (futureMinimumShiftedExponent O anchor)
      (futureMinimumShiftedValue O anchor) := by
  intro m
  have hStep := O.step (anchor + m)
  refine ⟨O.exponent_pos (anchor + m), O.value_odd (anchor + m), ?_⟩
  dsimp [futureMinimumShiftedExponent, futureMinimumShiftedValue]
  have hEq := hStep.equation
  simpa [Nat.add_assoc] using hEq

/--
Global CST の標準 future-minimum block は、純整数側の `IsAdmissibleBlock` を満たす。
-/
theorem nextFutureMinimum_isAdmissibleBlock_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    IsAdmissibleBlock (O.segmentWord i (j - i)) := by
  have hLen : 0 < j - i := Nat.sub_pos_of_lt hNext.1
  refine ⟨?_, O.segmentWord_valid i (j - i), ?_, ?_⟩
  · change 0 < Word.oddSteps (O.segmentWord i (j - i))
    simpa using hLen
  · have hTwo :=
      O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
        G hStart hNext
    have hWordLen :
        (O.segmentWord i (j - i)).length = j - i := by
      exact O.segmentWord_length i (j - i)
    rw [hWordLen]
    exact hTwo
  · intro q hqPos hqLt
    have hWholeLen :
        (O.segmentWord i (j - i)).length = j - i := by
      have hOdd := O.segmentWord_oddSteps i (j - i)
      simp only [OddOrbit.segmentWord_length]
    rw [hWholeLen] at hqLt
    let k : ℕ := j - q
    have hiK : i < k := by
      dsimp [k]
      omega
    have hkJ : k < j := by
      dsimp [k]
      omega
    have hCritical :=
      O.nextFutureMinimum_properSuffix_criticalTwoDepth_le SInf hNext hiK hkJ
    have hStartEq : i + ((j - i) - q) = k := by
      dsimp [k]
      omega
    have hSuffixWord :
        (O.segmentWord i (j - i)).drop ((j - i) - q) =
          O.segmentWord k q := by
      have hSplit := O.segmentWord_add i ((j - i) - q) q
      have hLenSplit : (j - i) - q + q = j - i := by omega
      rw [hLenSplit] at hSplit
      rw [hSplit]
      have hPrefixLen :
          (O.segmentWord i ((j - i) - q)).length = (j - i) - q := by
        have hOdd := O.segmentWord_oddSteps i ((j - i) - q)
        simp only [OddOrbit.segmentWord_length]
      simp [hPrefixLen, hStartEq]
    unfold suffixTwoDepth
    rw [hWholeLen, hSuffixWord]
    unfold Critical.criticalTwoDepth at hCritical
    have hJK : j - k = q := by
      dsimp [k]
      omega
    simpa [hJK] using hCritical

/--
標準 future-minimum tail は pure integer 側で許容 block decomposition を与える。
-/
theorem futureMinima_isAdmissibleDecomposition_of_globalCST
    (O : Collatz3.OddOrbit)
    (F : O.FutureMinima)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (start : ℕ) :
    IsAdmissibleDecomposition
      (futureMinimumShiftedExponent O (F.index start))
      (futureMinimumLengthFrom F start) := by
  intro n
  have hNext :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard (start + n)
  have hStartMin := F.minimum (start + n)
  have hBoundary := boundaryIndex_futureMinimumLengthFrom F start n
  have hAnchorLe : F.index start ≤ F.index (start + n) := by
    apply F.index_strict.monotone
    omega
  have hStartEq :
      F.index start + boundaryIndex (futureMinimumLengthFrom F start) n =
        F.index (start + n) := by
    rw [hBoundary]
    exact Nat.add_sub_of_le hAnchorLe
  have hWord :=
    streamWord_futureMinimumShiftedExponent
      O (F.index start)
      (boundaryIndex (futureMinimumLengthFrom F start) n)
      (futureMinimumLengthFrom F start n)
  rw [hStartEq] at hWord
  rw [hWord]
  simpa [futureMinimumLengthFrom] using
    nextFutureMinimum_isAdmissibleBlock_of_globalCST
      O G SInf hStartMin hNext

/--
A 型 linear defect lower bound は、late future minimum から shift した pure integer stream へ
`2*K` の係数で移る。

ここでは boundary だけでなく全 shifted index に対する existing theorem をそのまま使う。
-/
theorem exists_pureLinearDefect_after_futureMinimum_of_linearDefect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N anchor : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ anchor)
    (hAnchor : O.FutureMinimumAt anchor) :
    ∃ R : ℕ,
      ∀ m : ℕ,
        R ≤ m →
          m ≤ 2 * K * streamDefect (futureMinimumShiftedExponent O anchor) m := by
  obtain ⟨R, hShift⟩ :=
    O.exists_shift_linearDefectLowerBound_two_mul_of_linearDefect
      G SInf hLinear hLate hAnchor
  refine ⟨R, ?_⟩
  intro m hm
  have hMain := hShift.2 m hm
  have hDepthEq :
      prefixDepth (futureMinimumShiftedExponent O anchor) m =
        infinitePrefixDepth (O.shift anchor).exponent m := by
    clear hm hMain
    induction m with
    | zero =>
        simp [prefixDepth, prefixWord, infinitePrefixDepth]
    | succ m ih =>
        rw [prefixDepth_succ, infinitePrefixDepth_succ, ih]
        change
          infinitePrefixDepth (O.shift anchor).exponent m +
              O.exponent (anchor + m) =
            infinitePrefixDepth (O.shift anchor).exponent m +
              O.exponent (anchor + m)
        rfl
  unfold streamDefect
  unfold infiniteSurvivorDefect at hMain
  rw [hDepthEq]
  exact hMain

end IntegerReduction
end Collatz3
