import CollatzLean.Collatz3.CSTConditional.FutureMinimumLocalRoof
import CollatzLean.Collatz3.Semantics.StandardFutureMinimum

/-!
# Collatz3 CSTConditional: fixed-anchor local roof defect の Beatty carry cocycle

`futureMinimum_localRoofDefect O i r` は fixed future minimum `i` から長さ `r` の segment を見た
Beatty roof との差である。

このファイルでは新しい state を導入せず、segment の連結と Beatty roof の加法公式だけから
local roof defect の exact cocycle を導く。

重要なのは途中点も future minimum である場合である。このとき前半・後半の両 segment で
`twoSteps ≤ beattyIndex` が保証され、`Nat.sub` は本当の整数差として働く。

長さ `a`,`b` を連結すると

`d_i(a+b) = d_i(a) + d_(i+a)(b) + beattyCarry(a,b)`。

さらに `i+a` から `i+a+b` が next future minimum block なら moving-anchor defect は `0` なので

`d_i(a+b) = d_i(a) + beattyCarry(a,b)`。

標準 future-minimum 列ではこれを反復でき、fixed anchor から見た endpoint depth は
0/1 Beatty carry の有限和に exact に一致する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
actual orbit の segment word は長さの加法に沿って exact に連結する。
-/
theorem segmentWord_add_eq_append
    (O : Collatz3.OddOrbit)
    (start a b : ℕ) :
    O.segmentWord start (a + b) =
      O.segmentWord start a ++ O.segmentWord (start + a) b := by
  induction a generalizing start with
  | zero =>
      simp
  | succ a ih =>
      rw [show (a + 1) + b = (a + b) + 1 by omega]
      simp only [segmentWord_succ, List.cons_append]
      rw [ih (start := start + 1)]
      simp [Nat.add_comm, Nat.add_left_comm]

/--
segment の total two-depth も length split に沿って exact に加法分解する。
-/
theorem segmentTwoSteps_add_eq
    (O : Collatz3.OddOrbit)
    (start a b : ℕ) :
    Word.twoSteps (O.segmentWord start (a + b)) =
      Word.twoSteps (O.segmentWord start a) +
        Word.twoSteps (O.segmentWord (start + a) b) := by
  rw [O.segmentWord_add_eq_append start a b]
  simp

/--
Global CST 下で、開始点 `start` と途中点 `start+a` がともに future minimum なら
local roof defect は Beatty carry を加えた exact cocycle を満たす。

`d_start(a+b) = d_start(a) + d_(start+a)(b) + carry(a,b)`。
-/
theorem futureMinimum_localRoofDefect_add_cocycle_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (a b : ℕ)
    (hMiddle : O.FutureMinimumAt (start + a)) :
    O.futureMinimum_localRoofDefect start (a + b) =
      O.futureMinimum_localRoofDefect start a +
        O.futureMinimum_localRoofDefect (start + a) b +
          Critical.beattyCarry a b := by
  have hWhole :=
    O.segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
      G hStart (a + b)
  have hLeft :=
    O.segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
      G hStart a
  have hRight :=
    O.segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
      G hMiddle b
  have hSegment := O.segmentTwoSteps_add_eq start a b
  have hBeatty := Critical.beattyIndex_add_eq a b
  omega

/--
Global CST 下では next future minimum block の moving-anchor local roof defect は `0`。
-/
theorem futureMinimum_localRoofDefect_eq_zero_of_nextFutureMinimum_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    O.futureMinimum_localRoofDefect i (j - i) = 0 := by
  have hEq :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  exact
    (O.futureMinimum_localRoofDefect_eq_zero_iff_segmentTwoSteps_eq_beattyIndex
      G hStart (j - i)).2 hEq

/--
fixed future minimum `i` から見て、途中の future minimum `j` の次の標準 block が `k` へ進むとき、
endpoint local roof defect は一個の Beatty carry だけ増える。

`d_i(k-i) = d_i(j-i) + carry(j-i, k-j)`。

moving anchor `j` から見た block defect が `0` であることを cocycle に代入した式。
-/
theorem futureMinimumEndpoint_localRoofDefect_step
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j k : ℕ}
    (hij : i ≤ j)
    (hI : O.FutureMinimumAt i)
    (hJ : O.FutureMinimumAt j)
    (hNext : O.NextFutureMinimum j k) :
    O.futureMinimum_localRoofDefect i (k - i) =
      O.futureMinimum_localRoofDefect i (j - i) +
        Critical.beattyCarry (j - i) (k - j) := by
  have hjk : j < k := hNext.1
  have hia : i + (j - i) = j := Nat.add_sub_of_le hij
  have hab : (j - i) + (k - j) = k - i := by omega
  have hMiddle : O.FutureMinimumAt (i + (j - i)) := by
    rw [hia]
    exact hJ
  have hCocycle :=
    O.futureMinimum_localRoofDefect_add_cocycle_of_globalCST
      G hI (j - i) (k - j) hMiddle
  have hZero :=
    O.futureMinimum_localRoofDefect_eq_zero_of_nextFutureMinimum_of_globalCST
      G hJ hNext
  rw [hia, hZero, Nat.add_zero] at hCocycle
  rw [hab] at hCocycle
  exact hCocycle

namespace FutureMinima

/--
標準 future-minimum 列の任意の selector position `base` を fixed anchor にする。
そこから `q` transitions 進んだ endpoint からさらに一段進むと、
fixed-anchor local roof defect は exact に一個の Beatty carry だけ増える。
-/
theorem fixedAnchor_localRoofDefect_succ_eq_add_beattyCarry
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (hStandard : F.IsStandard)
    (G : GlobalCST)
    (base q : ℕ) :
    O.futureMinimum_localRoofDefect (F.index base)
        (F.index (base + (q + 1)) - F.index base) =
      O.futureMinimum_localRoofDefect (F.index base)
          (F.index (base + q) - F.index base) +
        Critical.beattyCarry
          (F.index (base + q) - F.index base)
          (F.index (base + (q + 1)) - F.index (base + q)) := by
  have hBaseIndex : base ≤ base + q := by omega
  have hBaseLe : F.index base ≤ F.index (base + q) :=
    F.index_strict.monotone hBaseIndex
  have hNext :
      O.NextFutureMinimum
        (F.index (base + q))
        (F.index ((base + q) + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard (base + q)
  have hStep :=
    O.futureMinimumEndpoint_localRoofDefect_step
      G hBaseLe (F.minimum base) (F.minimum (base + q)) hNext
  simpa [show base + (q + 1) = (base + q) + 1 by omega] using hStep

/--
標準 future-minimum 列の任意の fixed anchor から見た endpoint defect は
Beatty carry の有限累積そのもの。

selector position `base` から `q` transitions 後までの local roof depth は

`sum_{t<q} carry(index(base+t)-index(base), index(base+t+1)-index(base+t))`。

各 carry は既存定理により `0` または `1` なので、fixed-anchor Ferrers depth を
純粋な 0/1 carry word として読める。
-/
theorem fixedAnchor_localRoofDefect_eq_sum_beattyCarry
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (hStandard : F.IsStandard)
    (G : GlobalCST)
    (base q : ℕ) :
    O.futureMinimum_localRoofDefect (F.index base)
        (F.index (base + q) - F.index base) =
      ∑ t ∈ Finset.range q,
        Critical.beattyCarry
          (F.index (base + t) - F.index base)
          (F.index (base + (t + 1)) - F.index (base + t)) := by
  induction q with
  | zero =>
      simp [futureMinimum_localRoofDefect]
  | succ q ih =>
      rw [F.fixedAnchor_localRoofDefect_succ_eq_add_beattyCarry
        hStandard G base q]
      rw [Finset.sum_range_succ]
      rw [ih]

/--
各 Beatty carry が `0/1` なので、任意の fixed anchor から `q` transitions 後の
local roof defect は高々 `q`。
-/
theorem fixedAnchor_localRoofDefect_le_transitionCount
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (hStandard : F.IsStandard)
    (G : GlobalCST)
    (base q : ℕ) :
    O.futureMinimum_localRoofDefect (F.index base)
        (F.index (base + q) - F.index base) ≤ q := by
  rw [F.fixedAnchor_localRoofDefect_eq_sum_beattyCarry hStandard G base q]
  calc
    (∑ t ∈ Finset.range q,
        Critical.beattyCarry
          (F.index (base + t) - F.index base)
          (F.index (base + (t + 1)) - F.index (base + t)))
        ≤ ∑ _t ∈ Finset.range q, 1 := by
          apply Finset.sum_le_sum
          intro t _ht
          exact Critical.beattyCarry_le_one _ _
    _ = q := by simp

end FutureMinima
end OddOrbit
end Collatz3
