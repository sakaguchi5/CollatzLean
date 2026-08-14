import CollatzLean.Collatz2.Canonical.ZeroCoreDualGap
import Mathlib.Data.Nat.Log
import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.External.TwoThreeGap

/-!
# Collatz2 Canonical: long nested canonical corridor

dual endpoint gap

  G*T < sigma*3^m

を suffix replay quotient に直接使う。

tail `v` の先頭から `r` 文字落とした actual suffix の replay quotient を `q_r` とする。

`q_r > 0` なら finish equation から

  T >= 2*3^(m-r)

なので

  2*G < sigma*3^r.

従って逆に

  sigma*3^r <= 2*G
  -----------------
  q_r = 0

が branch-free に成立する。

この条件が `r <= R` で一括成立すると

  actual boundary_r = canonicalStart(v.drop r)
  canonicalEnd(v.drop r) = T

が全段で成立する nested canonical corridor を得る。

さらに polynomial-relative 2-3 gap を入れると、
最後 `q` 文字だけを残して depth `m-q` まで corridor が延びるための
pure polynomial/exponential criterion を与える。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn
namespace CanonicalZeroCoreData

/-- segment を `r` step drop した後半 segment。 -/
private theorem segment_drop_of_le_local
    (O : OddOrbit)
    {i n r : ℕ}
    (hr : r ≤ n) :
    (O.segment i n).drop r =
      O.segment (i + r) (n - r) := by
  have hsum :
      r + (n - r) = n := by
    omega
  have h :=
    O.segment_add i r (n - r)
  rw [hsum] at h
  rw [h]
  simp

/-- true zero-core tail は actual orbit segment そのもの。 -/
theorem tail_eq_actual_segment
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Z.natural.tail =
      O.segment
        (D.startIndex + 1)
        Z.natural.tail.length := by
  have hLenWord :=
    Z.natural.tail_length_add_one
  have hWordLen :=
    D.word_length
  have hLen :
      D.length =
        Z.natural.tail.length + 1 := by
    omega
  have hSeg :
      D.word =
        O.exponent D.startIndex ::
          O.segment
            (D.startIndex + 1)
            Z.natural.tail.length := by
    unfold CanonicalEndpointFloorContractingReturn.word
    rw [hLen]
    simp
  have hExp :=
    D.firstExponent_eq_one
  rw [hExp] at hSeg
  have hCons :
      1 :: Z.natural.tail =
        1 ::
          O.segment
            (D.startIndex + 1)
            Z.natural.tail.length := by
    rw [← Z.natural.word_eq]
    exact hSeg
  simpa using hCons

/-- `drop r` した tail suffix は対応する actual segment。 -/
theorem tail_drop_eq_actual_segment
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r ≤ Z.natural.tail.length) :
    Z.natural.tail.drop r =
      O.segment
        (D.startIndex + 1 + r)
        (Z.natural.tail.length - r) := by
  rw [Z.tail_eq_actual_segment]
  simpa [Nat.add_assoc] using
    segment_drop_of_le_local O
      (i := D.startIndex + 1)
      (n := Z.natural.tail.length)
      (r := r)
      hr

/--
任意の `r <= m` について、drop suffix は actual endpoint `T` まで走る。
-/
theorem tail_drop_runs_to_canonicalEnd
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r ≤ Z.natural.tail.length) :
    Runs
      (Z.natural.tail.drop r)
      (O.value (D.startIndex + 1 + r))
      (Word.canonicalEnd Z.natural.tail) := by
  have hDrop :=
    Z.tail_drop_eq_actual_segment hr
  have hRun :=
    O.runsSegment
      (D.startIndex + 1 + r)
      (Z.natural.tail.length - r)
  rw [← hDrop] at hRun
  have hLen :
      D.length =
        Z.natural.tail.length + 1 := by
    have hTail :=
      Z.natural.tail_length_add_one
    have hWord :=
      D.word_length
    omega
  have hIndex :
      (D.startIndex + 1 + r) +
          (Z.natural.tail.length - r) =
        D.startIndex + D.length := by
    omega
  have hEnd :
      O.value (D.startIndex + D.length) =
        Word.canonicalEnd Z.natural.tail := by
    calc
      O.value (D.startIndex + D.length)
          = Word.canonicalEnd D.word := by
              simpa [
                CanonicalEndpointFloorContractingReturn.word
              ] using D.endCanonical
      _ = Word.canonicalEnd Z.natural.tail :=
        Z.fullEnd_eq_tailEnd
  rw [hIndex, hEnd] at hRun
  simpa [Nat.add_assoc] using hRun

/-- `r < m` なら drop suffix は nonempty。 -/
theorem tail_drop_nonempty
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r < Z.natural.tail.length) :
    Z.natural.tail.drop r ≠ [] := by
  apply List.ne_nil_of_length_pos
  have hpos :
      0 < Z.natural.tail.length - r :=
    Nat.sub_pos_of_lt hr
  simpa using hpos

/--
actual `drop r` suffix の replay coordinate。
-/
def suffixReplayCoordinate
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (r : ℕ)
    (hr : r < Z.natural.tail.length) :
    Word.ReplayCoordinate
      (Z.natural.tail.drop r)
      (O.value (D.startIndex + 1 + r))
      (Word.canonicalEnd Z.natural.tail) :=
  Word.ReplayCoordinate.ofRuns
    (Z.tail_drop_runs_to_canonicalEnd (Nat.le_of_lt hr))
    (Z.tail_drop_nonempty hr)

/--
positive replay quotient なら、
drop suffix の fundamental endpoint 幅が full canonical endpoint 以下。
-/
theorem two_mul_threePow_drop_le_endpoint_of_positiveReplay
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r < Z.natural.tail.length)
    (hq :
      0 <
        (Z.suffixReplayCoordinate r hr).quotient) :
    2 * 3 ^ (Z.natural.tail.length - r) ≤
      Word.canonicalEnd Z.natural.tail := by
  let Q :=
    Z.suffixReplayCoordinate r hr
  have hFinish :=
    Q.finish_eq
  have hqPos :
      0 < Q.quotient := by
    simpa [Q] using hq
  have hqOne :
      1 ≤ Q.quotient := by
    exact hqPos
  have hMul :
      2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r) ≤
        2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r) *
          Q.quotient := by
    have h :=
      Nat.mul_le_mul_left
        (2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r))
        hqOne
    simpa using h
  have hReplayTermLeFinish :
      2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r) *
          Q.quotient ≤
        Word.canonicalEnd Z.natural.tail := by
    calc
      2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r) *
          Q.quotient
          ≤
        Word.canonicalEnd (Z.natural.tail.drop r) +
          2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r) *
            Q.quotient := by
              omega
      _ = Word.canonicalEnd Z.natural.tail :=
        hFinish.symm
  have hLowerRaw :
      2 * 3 ^ Word.oddSteps (Z.natural.tail.drop r) ≤
        Word.canonicalEnd Z.natural.tail :=
    le_trans hMul hReplayTermLeFinish
  simpa [Word.oddSteps] using hLowerRaw

/--
positive replay quotient から、
full gap を掛けた scaled inequality を得る。
-/
theorem scaledGap_lt_sigma_threePow_of_positiveReplay
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r < Z.natural.tail.length)
    (hq :
      0 <
        (Z.suffixReplayCoordinate r hr).quotient) :
    (AffineTransfer.ofWord D.word).centerGap *
        (2 * 3 ^ (Z.natural.tail.length - r)) <
      Z.sigma *
        3 ^ Word.oddSteps Z.natural.tail := by
  have hLower :
      2 * 3 ^ (Z.natural.tail.length - r) ≤
        Word.canonicalEnd Z.natural.tail :=
    Z.two_mul_threePow_drop_le_endpoint_of_positiveReplay
      hr hq
  have hScaledLower :
      (AffineTransfer.ofWord D.word).centerGap *
          (2 * 3 ^ (Z.natural.tail.length - r)) ≤
        (AffineTransfer.ofWord D.word).centerGap *
          Word.canonicalEnd Z.natural.tail :=
    Nat.mul_le_mul_left
      (AffineTransfer.ofWord D.word).centerGap
      hLower
  exact
    lt_of_le_of_lt
      hScaledLower
      Z.dualEndpointGap

/--
`r ≤ L` のとき、

`G * (2 * 3^(L-r)) < sigma * 3^L`

から共通因子 `3^(L-r)` を消して

`2*G < sigma*3^r`

を得る。
-/
theorem two_mul_lt_sigma_threePow_of_scaled_threePow_lt
    {G sigma L r : ℕ}
    (hr : r ≤ L)
    (hScaled :
      G * (2 * 3 ^ (L - r)) <
        sigma * 3 ^ L) :
    2 * G < sigma * 3 ^ r := by
  have hSplit :
      L = (L - r) + r := by
    omega
  have hFactor :
      0 < 3 ^ (L - r) :=
    Nat.pow_pos (by omega)
  have hExp : L - r + r - r = L - r := by
    omega
  have hCommon :
      3 ^ (L - r) * (2 * G) <
        3 ^ (L - r) * (sigma * 3 ^ r) := by
    calc
      3 ^ (L - r) * (2 * G)
          =
        G * (2 * 3 ^ (L - r)) := by
          ring
      _ < sigma * 3 ^ L := hScaled
      _ =
        3 ^ (L - r) * (sigma * 3 ^ r) := by
          rw [hSplit, pow_add]
          rw [hExp]
          ring_nf
  exact
    (Nat.mul_lt_mul_left hFactor).mp hCommon


/--
positive replay quotient なら

  `2*G < sigma*3^r`.

full dual endpoint gap と finish replay equation だけを使う。
-/
theorem positiveReplay_implies_twoGap_lt_sigma_mul_threePow
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r < Z.natural.tail.length)
    (hq :
      0 <
        (Z.suffixReplayCoordinate r hr).quotient) :
    2 * (AffineTransfer.ofWord D.word).centerGap <
      Z.sigma * 3 ^ r := by
  have hScaled :
      (AffineTransfer.ofWord D.word).centerGap *
          (2 * 3 ^ (Z.natural.tail.length - r)) <
        Z.sigma *
          3 ^ Word.oddSteps Z.natural.tail :=
    Z.scaledGap_lt_sigma_threePow_of_positiveReplay
      hr hq
  have hOddStepsTail :
      Word.oddSteps Z.natural.tail =
        Z.natural.tail.length := by
    rfl
  rw [hOddStepsTail] at hScaled
  exact
    two_mul_lt_sigma_threePow_of_scaled_threePow_lt
      (G := (AffineTransfer.ofWord D.word).centerGap)
      (sigma := Z.sigma)
      (L := Z.natural.tail.length)
      (r := r)
      (Nat.le_of_lt hr)
      hScaled
/--
`σ*3^r <= 2G` なら replay quotient は0。
-/
theorem replay_eq_zero_of_sigma_mul_threePow_le_twoGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {r : ℕ}
    (hr : r < Z.natural.tail.length)
    (hBound :
      Z.sigma * 3 ^ r ≤
        2 * (AffineTransfer.ofWord D.word).centerGap) :
    (Z.suffixReplayCoordinate r hr).quotient = 0 := by
  by_contra hne
  have hq :
      0 <
        (Z.suffixReplayCoordinate r hr).quotient :=
    Nat.pos_of_ne_zero hne
  have hlt :=
    Z.positiveReplay_implies_twoGap_lt_sigma_mul_threePow
      hr hq
  omega


/--
effective `19/12` linear gap により first inner replay (`r=1`) は0。
-/
theorem firstInnerReplay_eq_zero_of_nineteenLinearGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    ∃ hOne : 1 < Z.natural.tail.length,
      (Z.suffixReplayCoordinate 1 hOne).quotient = 0 := by
  have hSpec :=
    Z.oddSteps_eq_six_mul_n_add_sigma
  have hsigma :=
    Z.sigma_pos
  have hn :=
    Z.natural.n_pos
  have hWholeTail :=
    Z.wholeOddSteps_eq_tailOddSteps_add_one
  have hOne :
      1 < Z.natural.tail.length := by
    have hTailOdd :
        Word.oddSteps Z.natural.tail =
          Z.natural.tail.length := by
      rfl
    rw [hTailOdd] at hWholeTail
    omega
  have hThree :=
    Z.three_mul_sigma_lt_two_mul_G_of_linearGap
      hEffective
  refine ⟨hOne, ?_⟩
  apply
    Z.replay_eq_zero_of_sigma_mul_threePow_le_twoGap
      hOne
  norm_num
  omega

/--
depth `R` までの nested canonical corridor。

各 `r <= R` で actual boundary が `canonicalStart(tail.drop r)` に一致し、
全 drop word の canonical endpoint が同じ terminal `T` に一致する。
-/
structure NestedCanonicalCorridor
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (depth : ℕ) : Prop where
  depth_lt_tail :
    depth < Z.natural.tail.length

  boundaryCanonical :
    ∀ r : ℕ,
      r ≤ depth →
      O.value (D.startIndex + 1 + r) =
        Word.canonicalStart (Z.natural.tail.drop r)

  endpointCanonical :
    ∀ r : ℕ,
      r ≤ depth →
      Word.canonicalEnd (Z.natural.tail.drop r) =
        Word.canonicalEnd Z.natural.tail

namespace NestedCanonicalCorridor

/-- corridor の各段は replay quotient 0。 -/
theorem replay_zero
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {Z : CanonicalZeroCoreData D}
    {R : ℕ}
    (C : NestedCanonicalCorridor Z R)
    {r : ℕ}
    (hr : r ≤ R) :
    (Z.suffixReplayCoordinate r
      (lt_of_le_of_lt hr C.depth_lt_tail)).quotient = 0 := by
  let Q :=
    Z.suffixReplayCoordinate r
      (lt_of_le_of_lt hr C.depth_lt_tail)
  apply Q.quotient_eq_zero_of_start_eq_canonical
  exact C.boundaryCanonical r hr

end NestedCanonicalCorridor

/--
`σ*3^R <= 2G` なら depth `R` まで一括で nested canonical。
-/
theorem nestedCanonicalCorridor_of_sigma_mul_threePow_le_twoGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    {R : ℕ}
    (hR : R < Z.natural.tail.length)
    (hBound :
      Z.sigma * 3 ^ R ≤
        2 * (AffineTransfer.ofWord D.word).centerGap) :
    NestedCanonicalCorridor Z R := by
  refine {
    depth_lt_tail := hR
    boundaryCanonical := ?_
    endpointCanonical := ?_
  }
  · intro r hrR
    have hrTail :
        r < Z.natural.tail.length :=
      lt_of_le_of_lt hrR hR
    have hPow :
        3 ^ r ≤ 3 ^ R :=
      Nat.pow_le_pow_right
        (by omega : 0 < (3 : ℕ)) hrR
    have hScaled :
        Z.sigma * 3 ^ r ≤
          Z.sigma * 3 ^ R :=
      Nat.mul_le_mul_left Z.sigma hPow
    have hBoundR :
        Z.sigma * 3 ^ r ≤
          2 * (AffineTransfer.ofWord D.word).centerGap :=
      le_trans hScaled hBound
    let Q :=
      Z.suffixReplayCoordinate r hrTail
    have hZero :
        Q.quotient = 0 := by
      exact
        Z.replay_eq_zero_of_sigma_mul_threePow_le_twoGap
          hrTail hBoundR
    exact
      Q.start_eq_canonical_of_quotient_eq_zero hZero
  · intro r hrR
    have hrTail :
        r < Z.natural.tail.length :=
      lt_of_le_of_lt hrR hR
    have hPow :
        3 ^ r ≤ 3 ^ R :=
      Nat.pow_le_pow_right
        (by omega : 0 < (3 : ℕ)) hrR
    have hScaled :
        Z.sigma * 3 ^ r ≤
          Z.sigma * 3 ^ R :=
      Nat.mul_le_mul_left Z.sigma hPow
    have hBoundR :
        Z.sigma * 3 ^ r ≤
          2 * (AffineTransfer.ofWord D.word).centerGap :=
      le_trans hScaled hBound
    let Q :=
      Z.suffixReplayCoordinate r hrTail
    have hZero :
        Q.quotient = 0 := by
      exact
        Z.replay_eq_zero_of_sigma_mul_threePow_le_twoGap
          hrTail hBoundR
    have hEnd :=
      Q.finish_eq_canonical_of_quotient_eq_zero hZero
    exact hEnd.symm

/-- effective gap だけで depth 1 corridor。 -/
theorem firstInnerNestedCanonicalCorridor
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    NestedCanonicalCorridor Z 1 := by
  have hOnePack :=
    Z.firstInnerReplay_eq_zero_of_nineteenLinearGap
      hEffective
  rcases hOnePack with ⟨hOne, hZero⟩
  have hThree :=
    Z.three_mul_sigma_lt_two_mul_G_of_linearGap
      hEffective
  apply
    Z.nestedCanonicalCorridor_of_sigma_mul_threePow_le_twoGap
      hOne
  norm_num
  omega

/--
polynomial-relative gap から long corridor を作る criterion。

外部入力の witness `K,A` を固定すると、最後 `q` 文字を残す depth

  R = m - q

について

  sigma * K * (p+1)^A <= 6 * 3^q

なら depth `R` まで全 suffix replay が0。

`K*(p+1)^A` は polynomial なので、
この条件は概念的に `q = O(log p)` で満たされる形である。
-/
theorem exists_longNestedCanonicalCorridor_rule
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      0 < K ∧
      ∀ {O : OddOrbit}
        {D : CanonicalEndpointFloorContractingReturn O}
        (Z : CanonicalZeroCoreData D)
        (q : ℕ),
        0 < q →
        q ≤ Z.natural.tail.length →
        Z.sigma *
            (K * (Word.oddSteps D.word + 1) ^ A) ≤
          6 * 3 ^ q →
        NestedCanonicalCorridor
          Z (Z.natural.tail.length - q) := by
  rcases hPoly with ⟨K, A, hKpos, hBaker⟩
  refine ⟨K, A, hKpos, ?_⟩
  intro O D Z q hqPos hqLe hResidual
  let p := Word.oddSteps D.word
  let H := Word.twoSteps D.word
  let G := (AffineTransfer.ofWord D.word).centerGap
  let P := K * (p + 1) ^ A
  let R := Z.natural.tail.length - q
  have hpPos : 0 < p := by
    dsimp [p]
    have hlen :=
      D.word_nonempty
    have hlenPos :
        0 < D.word.length :=
      List.length_pos_iff.mpr hlen
    simpa [Word.oddSteps] using hlenPos
  have hContract :
      3 ^ p < 2 ^ H := by
    dsimp [p, H]
    exact
      (Word.contracting_iff_threePow_lt_twoPow).1
        D.contracting
  have hBaker0 :=
    hBaker p H hpPos hContract
  have hGapEq :
      2 ^ H - 3 ^ p = G := by
    dsimp [G, p, H]
    rfl
  rw [hGapEq] at hBaker0
  have hPpos : 0 < P := by
    dsimp [P]
    exact
      Nat.mul_pos hKpos
        (Nat.pow_pos (by omega))
  have hpTail :
      p = Z.natural.tail.length + 1 := by
    dsimp [p]
    have h :=
      Z.wholeOddSteps_eq_tailOddSteps_add_one
    simpa [Word.oddSteps] using h
  have hRlt :
      R < Z.natural.tail.length := by
    dsimp [R]
    omega
  have hqR :
      q + R = Z.natural.tail.length := by
    dsimp [R]
    omega
  have hResidual0 :
      Z.sigma * P ≤ 6 * 3 ^ q := by
    simpa [P, p] using hResidual
  have hResidualScaled :
      (Z.sigma * P) * 3 ^ R ≤
        (6 * 3 ^ q) * 3 ^ R :=
    Nat.mul_le_mul_right (3 ^ R) hResidual0
  have hResidualToFull :
      P * (Z.sigma * 3 ^ R) ≤
        6 * 3 ^ Z.natural.tail.length := by
    calc
      P * (Z.sigma * 3 ^ R)
          = (Z.sigma * P) * 3 ^ R := by
              ring
      _ ≤ (6 * 3 ^ q) * 3 ^ R :=
        hResidualScaled
      _ = 6 * (3 ^ q * 3 ^ R) := by
        ring
      _ = 6 * 3 ^ (q + R) := by
        rw [pow_add]
      _ = 6 * 3 ^ Z.natural.tail.length := by
        rw [hqR]
  have hBakerScaled :
      6 * 3 ^ Z.natural.tail.length ≤
        2 * P * G := by
    have hTwo :
        2 * 3 ^ p ≤ 2 * (P * G) :=
      Nat.mul_le_mul_left 2 hBaker0
    calc
      6 * 3 ^ Z.natural.tail.length
          = 2 * 3 ^ (Z.natural.tail.length + 1) := by
              rw [pow_succ]
              ring
      _ = 2 * 3 ^ p := by
        rw [hpTail]
      _ ≤ 2 * (P * G) := hTwo
      _ = 2 * P * G := by
        ring
  have hPCorridor :
      P * (Z.sigma * 3 ^ R) ≤
        P * (2 * G) := by
    calc
      P * (Z.sigma * 3 ^ R)
          ≤ 6 * 3 ^ Z.natural.tail.length :=
        hResidualToFull
      _ ≤ 2 * P * G :=
        hBakerScaled
      _ = P * (2 * G) := by
        ring
  have hBound :
      Z.sigma * 3 ^ R ≤ 2 * G :=
    Nat.le_of_mul_le_mul_left hPCorridor hPpos
  exact
    Z.nestedCanonicalCorridor_of_sigma_mul_threePow_le_twoGap
      hRlt (by simpa [G, R] using hBound)


/--
polynomial witness `K,A` に対する末尾 allowance。

  q = floor(log_3(sigma * K * (p+1)^A)) + 1

とする。
-/
def polynomialTailAllowance
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (K A : ℕ) : ℕ :=
  Nat.log 3
      (Z.sigma *
        (K * (Word.oddSteps D.word + 1) ^ A)) + 1

/-- allowance は常に正。 -/
theorem polynomialTailAllowance_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (K A : ℕ) :
    0 < Z.polynomialTailAllowance K A := by
  unfold polynomialTailAllowance
  omega

/--
polynomial gap の witness `K,A` に対して、logarithmic allowance を使う long corridor。

  q = log_3(sigma*K*(p+1)^A)+1
  q <= m
  --------------------------------
  NestedCanonicalCorridor depth (m-q)

従って最後 `q` 文字を除く全 drop suffix が同じ endpoint で canonical。
-/
theorem exists_logarithmicLongNestedCanonicalCorridor
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      0 < K ∧
      ∀ {O : OddOrbit}
        {D : CanonicalEndpointFloorContractingReturn O}
        (Z : CanonicalZeroCoreData D),
        Z.polynomialTailAllowance K A ≤
            Z.natural.tail.length →
        NestedCanonicalCorridor Z
          (Z.natural.tail.length -
            Z.polynomialTailAllowance K A) := by
  rcases
      exists_longNestedCanonicalCorridor_rule hPoly with
    ⟨K, A, hKpos, hRule⟩
  refine ⟨K, A, hKpos, ?_⟩
  intro O D Z hAllowance
  let y :=
    Z.sigma *
      (K * (Word.oddSteps D.word + 1) ^ A)
  let q := Z.polynomialTailAllowance K A
  have hqPos : 0 < q := by
    dsimp [q]
    exact Z.polynomialTailAllowance_pos K A
  have hyltRaw :=
    Nat.lt_pow_succ_log_self
      (by omega : 1 < (3 : ℕ)) y
  have hqEq :
      q = Nat.log 3 y + 1 := by
    dsimp [q, y]
    rfl
  have hylt :
      y < 3 ^ q := by
    rw [hqEq]
    simpa [Nat.succ_eq_add_one] using hyltRaw
  have hyLe :
      y ≤ 3 ^ q :=
    Nat.le_of_lt hylt
  have hScale :
      3 ^ q ≤ 6 * 3 ^ q := by
    have h :=
      Nat.mul_le_mul_right
        (3 ^ q)
        (by omega : 1 ≤ (6 : ℕ))
    simp only [Nat.ofNat_pos, pow_pos, le_mul_iff_one_le_left, Nat.one_le_ofNat]
  have hResidual :
      Z.sigma *
          (K * (Word.oddSteps D.word + 1) ^ A) ≤
        6 * 3 ^ q := by
    dsimp [y] at hyLe
    exact le_trans hyLe hScale
  have hqLe :
      q ≤ Z.natural.tail.length := by
    simpa [q] using hAllowance
  have hCorridor :=
    hRule Z q hqPos hqLe hResidual
  simpa [q] using hCorridor

end CanonicalZeroCoreData
end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
