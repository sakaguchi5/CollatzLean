import CollatzLean.Collatz2.Canonical.ZeroCoreDualGap
import CollatzLean.Collatz2.External.TwoThreeGap

/-!
# Collatz2 Mountain: polynomial start bound from the zero core

current A の true `j=0` zero core では

  G*T < sigma*3^(p-1)

が dual prefix budget から得られる。
一方 Baker / Matveev 型の polynomial relative gap

  3^p <= C*(p+1)^A*G

を掛け合わせると、`G>0` を消去して

  3*T < sigma*C*(p+1)^A.

さらに `S<T` と `p=6*n+sigma`, `n>0` から `sigma<p` なので

  3*S < C*(p+1)^(A+1)
  S+1 <= C*(p+1)^(A+1).

このファイルは、この stage 6 の polynomial start bound を
subtraction-free な自然数不等式として保持する。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
2--3 polynomial gap の witness と、そこから得られる current-A start upper bound。
-/
structure PolynomialStartBoundData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  gapConstant : ℕ
  gapExponent : ℕ
  gapConstant_pos : 0 < gapConstant

  three_mul_start_lt :
    3 * Word.canonicalStart D.word <
      gapConstant *
        (Word.oddSteps D.word + 1) ^ (gapExponent + 1)

namespace PolynomialStartBoundData

/-- stage 6 で山側へ渡す polynomial bound。 -/
def bound
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (P : PolynomialStartBoundData D) : ℕ :=
  P.gapConstant *
    (Word.oddSteps D.word + 1) ^ (P.gapExponent + 1)

/-- canonical start は正。 -/
theorem canonicalStart_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O} :
    0 < Word.canonicalStart D.word := by
  have h := O.value_pos D.startIndex
  have hEq :
      O.value D.startIndex = Word.canonicalStart D.word := by
    simpa [CanonicalEndpointFloorContractingReturn.word] using
      D.startCanonical
  rw [hEq] at h
  exact h

/-- `S+1 <= C*(p+1)^(A+1)`。 -/
theorem start_add_one_le_bound
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (P : PolynomialStartBoundData D) :
    Word.canonicalStart D.word + 1 ≤ P.bound := by
  have hSpos := canonicalStart_pos (O := O) (D := D)
  have h := P.three_mul_start_lt
  unfold bound
  omega

/-- polynomial bound 自身は正。 -/
theorem bound_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (P : PolynomialStartBoundData D) :
    0 < P.bound := by
  have h := P.start_add_one_le_bound
  have hS := canonicalStart_pos (O := O) (D := D)
  omega

end PolynomialStartBoundData

namespace CanonicalZeroCoreData

/--
## Stage 6

polynomial 2--3 gap から current zero-core start の polynomial upper bound を構成する。
-/
theorem exists_polynomialStartBoundData
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hPoly : External.TwoThreeGapPolynomialBound) :
    Nonempty (PolynomialStartBoundData D) := by
  rcases hPoly with ⟨C, A, hCpos, hGap⟩
  let p := Word.oddSteps D.word
  let H := Word.twoSteps D.word
  let G := (AffineTransfer.ofWord D.word).centerGap
  let T := Word.canonicalEnd Z.natural.tail
  let P := C * (p + 1) ^ A
  have hpPos : 0 < p := by
    dsimp [p]
    have hlen : 0 < D.word.length :=
      List.length_pos_iff.mpr D.word_nonempty
    simpa [Word.oddSteps] using hlen
  have hContract : 3 ^ p < 2 ^ H := by
    dsimp [p, H]
    exact
      (Word.contracting_iff_threePow_lt_twoPow).1
        D.contracting
  have hPolyGap : 3 ^ p ≤ P * G := by
    have h := hGap p H hpPos hContract
    have hGapEq :
        2 ^ H - 3 ^ p = G := by
      dsimp [G, p, H]
      rfl
    rw [hGapEq] at h
    simpa [P] using h
  have hGpos : 0 < G := by
    dsimp [G]
    exact Z.fullGap_pos
  have hPpos : 0 < P := by
    dsimp [P]
    exact Nat.mul_pos hCpos (Nat.pow_pos (by omega))
  have hpTail :
      p = Word.oddSteps Z.natural.tail + 1 := by
    dsimp [p]
    exact Z.wholeOddSteps_eq_tailOddSteps_add_one
  have hDual : G * T < Z.sigma * 3 ^ Word.oddSteps Z.natural.tail := by
    simpa [G, T] using Z.dualEndpointGap
  have hScaledDual :
      G * (3 * T) < G * (Z.sigma * P) := by
    calc
      G * (3 * T)
          = 3 * (G * T) := by ring
      _ < 3 * (Z.sigma * 3 ^ Word.oddSteps Z.natural.tail) :=
        Nat.mul_lt_mul_of_pos_left hDual (by omega)
      _ = Z.sigma * 3 ^ p := by
        rw [hpTail, pow_succ]
        ring
      _ ≤ Z.sigma * (P * G) :=
        Nat.mul_le_mul_left Z.sigma hPolyGap
      _ = G * (Z.sigma * P) := by ring
  have hT : 3 * T < Z.sigma * P :=
    (Nat.mul_lt_mul_left hGpos).mp hScaledDual
  have hEndEq :
      Word.canonicalEnd D.word = T := by
    dsimp [T]
    exact Z.fullEnd_eq_tailEnd
  have hST : Word.canonicalStart D.word < T := by
    rw [← hEndEq]
    exact D.canonicalPositive
  have hSigmaLtP : Z.sigma < p := by
    have hSpec := Z.oddSteps_eq_six_mul_n_add_sigma
    have hn := Z.natural.n_pos
    dsimp [p] at hSpec ⊢
    omega
  have hSigmaLtSucc : Z.sigma < p + 1 := by
    omega
  have hSigmaP :
      Z.sigma * P < (p + 1) * P :=
    Nat.mul_lt_mul_of_pos_right hSigmaLtSucc hPpos
  have hPolyFinal :
      (p + 1) * P = C * (p + 1) ^ (A + 1) := by
    dsimp [P]
    rw [pow_succ]
    ring
  have hStart :
      3 * Word.canonicalStart D.word <
        C * (p + 1) ^ (A + 1) := by
    calc
      3 * Word.canonicalStart D.word
          < 3 * T :=
        Nat.mul_lt_mul_of_pos_left hST (by omega)
      _ < Z.sigma * P := hT
      _ < (p + 1) * P := hSigmaP
      _ = C * (p + 1) ^ (A + 1) := hPolyFinal
  let Q : PolynomialStartBoundData D := {
    gapConstant := C
    gapExponent := A
    gapConstant_pos := hCpos
    three_mul_start_lt := by
      simpa [p] using hStart
  }
  exact ⟨Q⟩

/-- existential witness を直接取り出す stage-6 版。 -/
theorem exists_polynomialStartBound
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ C A : ℕ,
      0 < C ∧
      Word.canonicalStart D.word + 1 ≤
        C * (Word.oddSteps D.word + 1) ^ (A + 1) := by
  obtain ⟨P⟩ := Z.exists_polynomialStartBoundData hPoly
  exact
    ⟨P.gapConstant, P.gapExponent, P.gapConstant_pos,
      by simpa [PolynomialStartBoundData.bound] using P.start_add_one_le_bound⟩

end CanonicalZeroCoreData
end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
