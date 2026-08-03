import CollatzLean.CollatzSecondLayer.MovingCompactness
import Mathlib.Tactic.Linarith

/-!
# moving compactnessの定量的帰結

第一bridgeで得たfuture-minimum性を使い、極限指数語の先頭指数と
有限prefixの総2除算数を定量化する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/--
future-minimumからoffset `k`だけ進んだ位置から長さ`m`を切ると、
総2除算数は`m*(k+m+1)`以下である。
-/
theorem segmentWord_twoSteps_le_quadratic
    (O : OddOrbit)
    {n : ℕ}
    (hmin : O.FutureMinimumAt n) :
    ∀ k m : ℕ,
      twoSteps (O.segmentWord (n + k) m) ≤
        m * (k + m + 1) := by
  intro k m
  induction m generalizing k with
  | zero =>
      simp [OddOrbit.segmentWord, twoSteps]
  | succ m ih =>
      have hhead :
          O.exponent (n + k) ≤ k + 2 := by
        simpa [Nat.add_assoc] using
          O.exponent_le_position_add_two hmin k
      have htail :
          twoSteps (O.segmentWord (n + (k + 1)) m) ≤
            m * ((k + 1) + m + 1) :=
        ih (k + 1)
      simp only [OddOrbit.segmentWord_succ, twoSteps_cons]
      rw [show n + k + 1 = n + (k + 1) by omega]
      nlinarith

/-- future-minimumから始まる長さ`m`語の総指数は`m*(m+1)`以下。 -/
theorem segmentWord_twoSteps_le_length_square
    (O : OddOrbit)
    {n : ℕ}
    (hmin : O.FutureMinimumAt n)
    (m : ℕ) :
    twoSteps (O.segmentWord n m) ≤ m * (m + 1) := by
  simpa using O.segmentWord_twoSteps_le_quadratic hmin 0 m

end OddOrbit

namespace MovingLimitData

/-- 非有界moving limitの極限指数語は先頭指数`1`を持つ。 -/
theorem limitExponent_zero_eq_one
    {O : OddOrbit}
    (D : MovingLimitData O) :
    D.limitExponent 0 = 1 := by
  obtain ⟨J, hJ⟩ := D.prefix_stabilizes 1
  obtain ⟨j, hjJ, hjLarge⟩ :=
    D.minima.eventually_large 1 J
  have he :
      O.exponent (D.minima.index j) = 1 :=
    O.exponent_eq_one_of_futureMinimum
      (D.minima.futureMinimum j) hjLarge
  have hword := hJ j hjJ
  have hsingle :
      [O.exponent (D.minima.index j)] =
        [D.limitExponent 0] := by
    simpa [OddOrbit.segmentWord, prefixWord] using hword
  injection hsingle with hcoord
  omega

/-- 極限語の長さ`m`prefixの総2除算数は二次式で抑えられる。 -/
theorem limitWord_twoSteps_le_quadratic
    {O : OddOrbit}
    (D : MovingLimitData O)
    (m : ℕ) :
    twoSteps (D.limitWord m) ≤ m * (m + 1) := by
  obtain ⟨J, hJ⟩ := D.prefix_stabilizes m
  have hword := hJ J le_rfl
  have hbound :=
    O.segmentWord_twoSteps_le_length_square
      (D.minima.futureMinimum J) m
  rw [hword] at hbound
  simpa [MovingLimitData.limitWord] using hbound

end MovingLimitData

end CollatzSecondLayer
