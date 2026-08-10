import CollatzLean.Collatz.Canonical.PrependOneCoreZeroObstruction
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.FirstCrossing

/-!
# quotient zero obstruction と adjacent first-crossing arithmetic の bridge

`j = 0` failure obstruction を、同じ actual adjacent first crossing から得る
`FirstCrossingArithmeticData` と接続する。

bridge では

* actual first-crossing word が `1 :: v`
* actual start がその full word の canonical start
* tail `v` が quotient-zero failure obstruction を持つ

ことを同一 witness 上で保持する。

ここから return gap を `2*n` と同定し、既存 adjacent first-crossing arithmetic の
`4 ≤ returnGap`, `13 ≤ length`, `3*returnGap < length`, 2-adic depth bound と、
Baker 型 polynomial endpoint bound を一つの必要条件 packet にまとめる。
最後に同じ packet を Exact / Late の二枝へ戻す。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/--
actual adjacent first crossing と prepend-one quotient-zero failure を
同一の canonical witness 上で接続する bridge。
-/
structure PrependOneZeroFirstCrossingBridge
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) where
  tail : Collatz.Word
  boundary : ℕ
  word_eq :
    R.word.take F.length = 1 :: tail
  zero :
    Word.PrependOneZeroFailureObstruction tail boundary
  start_eq :
    R.startValue = Word.canonicalStart (1 :: tail)

namespace PrependOneZeroFirstCrossingBridge

/-- bridge の actual first crossing を純整数 arithmetic data へ落とす。 -/
def arithmetic
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (_Z : PrependOneZeroFirstCrossingBridge F) :
    FirstCrossingArithmeticData (BlockArithmeticData.ofState R) :=
  FirstCrossingArithmeticData.ofFirstCrossing F

/-- arithmetic 側の word は同じ prepend-one word。 -/
theorem arithmetic_word_eq
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (Z : PrependOneZeroFirstCrossingBridge F) :
    Z.arithmetic.word = 1 :: Z.tail := by
  change R.word.take F.length = 1 :: Z.tail
  exact Z.word_eq

/-- arithmetic block start は full canonical start。 -/
theorem arithmetic_start_eq_canonicalStart
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (Z : PrependOneZeroFirstCrossingBridge F) :
    (BlockArithmeticData.ofState R).startValue =
      Word.canonicalStart (1 :: Z.tail) := by
  change R.startValue = Word.canonicalStart (1 :: Z.tail)
  exact Z.start_eq

/--
同じ word・同じ start の actual realization と canonical realization は
endpoint も一致する。
-/
theorem endpoint_eq_canonicalEnd
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (Z : PrependOneZeroFirstCrossingBridge F) :
    F.endpointValue = Word.canonicalEnd (1 :: Z.tail) := by
  have hActual := F.realizes
  rw [Z.word_eq] at hActual
  have hCanonical := Word.canonicalEnd_realizes (1 :: Z.tail)
  unfold Word.Realizes at hActual hCanonical
  rw [Z.start_eq] at hActual
  have hScaled :
      2 ^ Word.twoSteps (1 :: Z.tail) * F.endpointValue =
        2 ^ Word.twoSteps (1 :: Z.tail) *
          Word.canonicalEnd (1 :: Z.tail) :=
    hActual.trans hCanonical.symm
  exact
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      hScaled

/-- arithmetic endpoint も full canonical end と一致する。 -/
theorem arithmetic_endpoint_eq_canonicalEnd
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (Z : PrependOneZeroFirstCrossingBridge F) :
    Z.arithmetic.endpointValue = Word.canonicalEnd (1 :: Z.tail) := by
  change F.endpointValue = Word.canonicalEnd (1 :: Z.tail)
  exact Z.endpoint_eq_canonicalEnd

end PrependOneZeroFirstCrossingBridge

/--
quotient-zero adjacent first crossing に残る必要条件をまとめた packet。
`n` は canonical positive return `endpoint-start = 2*n` の witness。
-/
structure PrependOneZeroAdjacentNecessaryData
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (Z : PrependOneZeroFirstCrossingBridge F) where
  K : ℕ
  A : ℕ
  n : ℕ
  K_pos : 0 < K
  n_pos : 0 < n
  returnGap_eq_two_mul :
    Z.arithmetic.returnGap = 2 * n
  two_le_n : 2 ≤ n
  thirteen_le_length :
    13 ≤ Z.arithmetic.length
  six_mul_n_lt_length :
    6 * n < Z.arithmetic.length
  polynomialEndpointBound :
    3 * Z.arithmetic.endpointValue ≤
      (Z.arithmetic.length - 6 * n) *
        (K * (Z.arithmetic.length + 1) ^ A)
  returnDepthBound :
    ∀ D u : ℕ,
      TwoAdic.ExactFactor (2 * n) D u →
        3 * 2 ^ D < Z.arithmetic.length

namespace PrependOneZeroFirstCrossingBridge

/--
bridge と Baker 型 gap 入力から quotient-zero adjacent 必要条件 packet を作る。
-/
theorem existsNecessaryData
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    (Z : PrependOneZeroFirstCrossingBridge F)
    (hGap : External.TwoThreeGapPolynomialBound) :
    Nonempty (PrependOneZeroAdjacentNecessaryData Z) := by
  let Q := Z.arithmetic
  rcases Z.zero.paradoxical.exactReturn with
    ⟨n, hnPos, hCanonicalReturn, _hCanonicalExact⟩
  have hStart :
      (BlockArithmeticData.ofState R).startValue =
        Word.canonicalStart (1 :: Z.tail) :=
    Z.arithmetic_start_eq_canonicalStart
  have hEnd :
      Q.endpointValue = Word.canonicalEnd (1 :: Z.tail) := by
    simpa [Q] using Z.arithmetic_endpoint_eq_canonicalEnd
  have hGapEq : Q.returnGap = 2 * n := by
    have h := Q.endpoint_eq_start_add_gap
    rw [hEnd, hStart, hCanonicalReturn] at h
    omega
  have hTwoLeN : 2 ≤ n := by
    have hfour := Q.four_le_returnGap
    rw [hGapEq] at hfour
    omega
  have hSix : 6 * n < Q.length := by
    have hthree := Q.three_mul_returnGap_lt_length
    rw [hGapEq] at hthree
    nlinarith
  obtain ⟨K, A, hKPos, hPoly⟩ :=
    Q.endpoint_le_returnSlack_polynomial hGap
  have hSlack :
      Q.returnSlack = Q.length - 6 * n := by
    unfold FirstCrossingArithmeticData.returnSlack
    rw [hGapEq]
    have hmul : 3 * (2 * n) = 6 * n := by ring
    rw [hmul]
  rw [hSlack] at hPoly
  have hDepth :
      ∀ D u : ℕ,
        TwoAdic.ExactFactor (2 * n) D u →
          3 * 2 ^ D < Q.length := by
    intro D u hD
    apply Q.returnDepthBound D u
    rw [hGapEq]
    exact hD
  exact
    ⟨{
      K := K
      A := A
      n := n
      K_pos := hKPos
      n_pos := hnPos
      returnGap_eq_two_mul := hGapEq
      two_le_n := hTwoLeN
      thirteen_le_length := Q.thirteen_le_length
      six_mul_n_lt_length := hSix
      polynomialEndpointBound := hPoly
      returnDepthBound := hDepth
    }⟩

end PrependOneZeroFirstCrossingBridge

/-- quotient-zero packet を既存 actual first-crossing の Exact / Late 二枝へ戻す。 -/
inductive PrependOneZeroAdjacentExactLateOutcome
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    {Z : PrependOneZeroFirstCrossingBridge F}
    (P : PrependOneZeroAdjacentNecessaryData Z) : Type
  | exact
      (isExact : F.IsExact)
  | late
      (isLate : F.IsLate)

namespace PrependOneZeroAdjacentNecessaryData

/-- 必要条件 packet は既存の Exact または Late のどちらかへ必ず再分岐する。 -/
noncomputable def toExactLateOutcome
    {O : OddOrbit} {R : State O}
    {F : FirstCrossingData R}
    {Z : PrependOneZeroFirstCrossingBridge F}
    (P : PrependOneZeroAdjacentNecessaryData Z) :
    PrependOneZeroAdjacentExactLateOutcome P := by
  classical
  by_cases hExact : F.IsExact
  · exact
      PrependOneZeroAdjacentExactLateOutcome.exact hExact
  · have hLate : F.IsLate := by
      rcases F.exact_or_late with h | h
      · exact False.elim (hExact h)
      · exact h
    exact
      PrependOneZeroAdjacentExactLateOutcome.late hLate

end PrependOneZeroAdjacentNecessaryData

end IntegerObstruction
end AdjacentReturn
end Collatz
