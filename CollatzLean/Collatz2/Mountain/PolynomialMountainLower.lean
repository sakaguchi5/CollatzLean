import CollatzLean.Collatz2.Mountain.PolynomialStartBound
import CollatzLean.Collatz2.Mountain.FiniteHercher
import CollatzLean.Collatz2.Mountain.BarinaHercherLower
import Mathlib.Data.Nat.Log

/-!
# Collatz2 Mountain: polynomial start bound -> mountain-count lower bound

Stage 7。

一 mountain `x -> y` では Hercher Lemma 8 / Lemma 20 の整数形だけから

  y + 1 <= (x + 1)^2

が従う。
これを mountain chain 全体へ反復すると、mountain 数 `m` について

  2^p <= (S+1)^(2^m - 1).

Stage 6 の

  S+1 <= B := C*(p+1)^(A+1)

を入れれば

  2^p <= B^(2^m - 1).

最後に `q = clog_2(B)` とすると `B <= 2^q` なので

  p <= q * (2^m - 1).

従って任意の `M` について

  q * (2^M - 1) < p

を有限整数計算で証明できれば `M < m`。
この形なら explicit 2--3 gap 定数を後から入れるだけで mountain lower bound を
`native_decide` 型 certificate へ落とせる。
-/

namespace Collatz2

namespace Word.MountainRun

/--
一 mountain の valley growth を粗いが完全に整数的な平方 bound へ圧縮する。

  next + 1 <= (start + 1)^2.
-/
theorem next_add_one_le_start_add_one_sq
    {w : Word} {x y : ℕ}
    (M : Word.MountainRun w x y) :
    y + 1 ≤ (x + 1) ^ 2 := by
  let k := M.shape.oddRunLength
  have hHercher :
      2 ^ (k + 1) * y < 3 ^ k * (x + 1) := by
    simpa [k] using M.hercherLemma20_integer
  have hStartRaw : 2 ^ k - 1 ≤ x := by
    simpa [k] using M.hercherLemma8_mountain
  have hTwoPowLe : 2 ^ k ≤ x + 1 := by
    omega
  have hThreeFour : 3 ^ k ≤ 4 ^ k := by
    exact Nat.pow_le_pow_left (by omega : (3 : ℕ) ≤ 4) k
  have hFourEq : 4 ^ k = 2 ^ k * 2 ^ k := by
    calc
      4 ^ k = (2 * 2) ^ k := by norm_num
      _ = 2 ^ k * 2 ^ k := by rw [Nat.mul_pow]
  have hTwoSucc : 2 ^ k ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
  have hRhs :
      3 ^ k * (x + 1) ≤
        2 ^ (k + 1) * ((x + 1) ^ 2) := by
    calc
      3 ^ k * (x + 1)
          ≤ 4 ^ k * (x + 1) :=
        Nat.mul_le_mul_right (x + 1) hThreeFour
      _ = 2 ^ k * (2 ^ k * (x + 1)) := by
        rw [hFourEq]
        ring
      _ ≤ 2 ^ k * ((x + 1) * (x + 1)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_right (x + 1) hTwoPowLe
      _ ≤ 2 ^ (k + 1) * ((x + 1) * (x + 1)) :=
        Nat.mul_le_mul_right ((x + 1) * (x + 1)) hTwoSucc
      _ = 2 ^ (k + 1) * ((x + 1) ^ 2) := by ring
  have hScaled :
      2 ^ (k + 1) * y <
        2 ^ (k + 1) * ((x + 1) ^ 2) :=
    lt_of_lt_of_le hHercher hRhs
  have hPowPos : 0 < 2 ^ (k + 1) :=
    Nat.pow_pos (by omega)
  have hy : y < (x + 1) ^ 2 :=
    (Nat.mul_lt_mul_left hPowPos).mp hScaled
  omega

end Word.MountainRun

namespace Word.MountainDecomposition

/--
mountain block list と actual run から、odd-step exponent の二進 envelope を得る内部補題。
-/
private theorem list_twoPow_oddSteps_le_startEnvelope
    {blocks : List Word}
    {x z : ℕ}
    (hShape :
      ∀ b : Word, b ∈ blocks → Nonempty (Word.MountainBlock b))
    (hRun : Runs blocks.flatten x z) :
    2 ^ Word.oddSteps blocks.flatten ≤
      (x + 1) ^ (2 ^ blocks.length - 1) := by
  induction blocks generalizing x z with
  | nil =>
      simp [Word.oddSteps]
  | cons b bs ih =>
      have hRunAppend : Runs (b ++ bs.flatten) x z := by
        simpa using hRun
      obtain ⟨y, hRunB, hRunTail⟩ := Runs.split_append hRunAppend
      have hbMem : b ∈ b :: bs := by simp
      obtain ⟨Mb⟩ := hShape b hbMem
      let M : Word.MountainRun b x y := {
        shape := Mb
        run := hRunB
      }
      have hHead :
          2 ^ Word.oddSteps b ≤ x + 1 := by
        have h0 : 2 ^ Mb.oddRunLength - 1 ≤ x :=
          M.start_ge_twoPow_sub_one
        have hEq : Word.oddSteps b = Mb.oddRunLength :=
          Mb.oddSteps_eq
        rw [hEq]
        omega
      have hGrowth : y + 1 ≤ (x + 1) ^ 2 :=
        M.next_add_one_le_start_add_one_sq
      have hShapeTail :
          ∀ c : Word, c ∈ bs → Nonempty (Word.MountainBlock c) := by
        intro c hc
        exact hShape c (by simp [hc])
      have hTail :
          2 ^ Word.oddSteps bs.flatten ≤
            (y + 1) ^ (2 ^ bs.length - 1) :=
        ih hShapeTail hRunTail
      let E := 2 ^ bs.length - 1
      have hGrowthPow :
          (y + 1) ^ E ≤ ((x + 1) ^ 2) ^ E :=
        Nat.pow_le_pow_left hGrowth E
      have hTailBound :
          2 ^ Word.oddSteps bs.flatten ≤
            (x + 1) ^ (2 * E) := by
        calc
          2 ^ Word.oddSteps bs.flatten
              ≤ (y + 1) ^ E := by
                simpa [E] using hTail
          _ ≤ ((x + 1) ^ 2) ^ E := hGrowthPow
          _ = (x + 1) ^ (2 * E) := by
                rw [pow_mul]
      have hMul :
          2 ^ Word.oddSteps b *
              2 ^ Word.oddSteps bs.flatten ≤
            (x + 1) * (x + 1) ^ (2 * E) :=
        Nat.mul_le_mul hHead hTailBound
      have hExp :
          1 + 2 * E = 2 ^ (bs.length + 1) - 1 := by
        dsimp [E]
        rw [pow_succ]
        have hp : 0 < 2 ^ bs.length := Nat.pow_pos (by omega)
        omega
      have hOddAppend :
          Word.oddSteps (b :: bs).flatten =
            Word.oddSteps b + Word.oddSteps bs.flatten := by
        simp [Word.oddSteps]
      calc
        2 ^ Word.oddSteps (b :: bs).flatten
            =
          2 ^ Word.oddSteps b *
            2 ^ Word.oddSteps bs.flatten := by
              rw [hOddAppend, pow_add]
        _ ≤ (x + 1) * (x + 1) ^ (2 * E) := hMul
        _ = (x + 1) ^ (1 + 2 * E) := by
              have hOne : 1 + 2 * E = 2 * E + 1 := by omega
              rw [hOne, pow_succ]
              ring
        _ = (x + 1) ^ (2 ^ (b :: bs).length - 1) := by
              rw [show (b :: bs).length = bs.length + 1 by simp, ← hExp]

/--
## Mountain envelope

m 個の mountain からなる actual run `x -> z` では

  2^oddSteps(w) <= (x+1)^(2^m-1).
-/
theorem twoPow_oddSteps_le_startEnvelope
    {w : Word}
    (C : Word.MountainDecomposition w)
    {x z : ℕ}
    (hRun : Runs w x z) :
    2 ^ Word.oddSteps w ≤
      (x + 1) ^ (2 ^ C.mountainCount - 1) := by
  have hRaw :=
    list_twoPow_oddSteps_le_startEnvelope
      (blocks := C.blocks)
      C.shape
      (by simpa [C.decomp] using hRun)
  have hCount :
      C.mountainCount = C.blocks.length := by
    rfl
  simpa [C.decomp, hCount] using hRaw

end Word.MountainDecomposition

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
Stage 6 の start bound を mountain envelope へ代入する。
-/
theorem polynomialMountainEnvelope
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (P : PolynomialStartBoundData D)
    (C : Word.MountainDecomposition D.word) :
    2 ^ Word.oddSteps D.word ≤
      P.bound ^ (2 ^ C.mountainCount - 1) := by
  have hEnvelope :=
    C.twoPow_oddSteps_le_startEnvelope D.runsCanonical
  have hStart := P.start_add_one_le_bound
  have hPow :
      (Word.canonicalStart D.word + 1) ^
          (2 ^ C.mountainCount - 1) ≤
        P.bound ^ (2 ^ C.mountainCount - 1) :=
    Nat.pow_le_pow_left hStart (2 ^ C.mountainCount - 1)
  exact le_trans hEnvelope hPow

/-- polynomial bound を覆う最小2冪の exponent。 -/
def PolynomialStartBoundData.binaryExponent
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (P : PolynomialStartBoundData D) : ℕ :=
  Nat.clog 2 P.bound

/-- `bound <= 2^binaryExponent`。 -/
theorem PolynomialStartBoundData.bound_le_twoPow_binaryExponent
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (P : PolynomialStartBoundData D) :
    P.bound ≤ 2 ^ P.binaryExponent := by
  unfold PolynomialStartBoundData.binaryExponent
  exact Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) P.bound

/--
## Stage 7 compressed inequality

  p <= clog_2(B) * (2^m - 1).
-/
theorem oddSteps_le_binaryExponent_mul_mountainFactor
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (P : PolynomialStartBoundData D)
    (C : Word.MountainDecomposition D.word) :
    Word.oddSteps D.word ≤
      P.binaryExponent * (2 ^ C.mountainCount - 1) := by
  let E := 2 ^ C.mountainCount - 1
  let q := P.binaryExponent
  have hEnvelope :
      2 ^ Word.oddSteps D.word ≤ P.bound ^ E := by
    simpa [E] using D.polynomialMountainEnvelope P C
  have hBoundTwo : P.bound ≤ 2 ^ q := by
    simpa [q] using P.bound_le_twoPow_binaryExponent
  have hRaise :
      P.bound ^ E ≤ (2 ^ q) ^ E :=
    Nat.pow_le_pow_left hBoundTwo E
  have hToPow :
      2 ^ Word.oddSteps D.word ≤
        2 ^ (q * E) := by
    calc
      2 ^ Word.oddSteps D.word
          ≤ P.bound ^ E := hEnvelope
      _ ≤ (2 ^ q) ^ E := hRaise
      _ = 2 ^ (q * E) := by rw [pow_mul]
  have hLog :
      Word.oddSteps D.word ≤
        Nat.log 2 (2 ^ (q * E)) :=
    Nat.le_log_of_pow_le (by omega : 1 < (2 : ℕ)) hToPow
  rw [Nat.log_pow (by omega : 1 < (2 : ℕ))] at hLog
  simpa [q, E] using hLog

/--
finite integer certificate。
`M` mountain まででは RHS が `p` に届かないなら、actual mountain 数は `M` より大きい。
-/
theorem mountainCount_gt_of_binaryCertificate
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (P : PolynomialStartBoundData D)
    (C : Word.MountainDecomposition D.word)
    (M : ℕ)
    (hCert :
      P.binaryExponent * (2 ^ M - 1) <
        Word.oddSteps D.word) :
    M < C.mountainCount := by
  by_contra hnot
  have hm : C.mountainCount ≤ M := Nat.le_of_not_gt hnot
  have hPow :
      2 ^ C.mountainCount ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hm
  have hFactor :
      2 ^ C.mountainCount - 1 ≤ 2 ^ M - 1 :=
    Nat.sub_le_sub_right hPow 1
  have hScaled :
      P.binaryExponent * (2 ^ C.mountainCount - 1) ≤
        P.binaryExponent * (2 ^ M - 1) :=
    Nat.mul_le_mul_left P.binaryExponent hFactor
  have hMain :=
    D.oddSteps_le_binaryExponent_mul_mountainFactor P C
  omega

/--
`TwoThreeGapPolynomialBound` の existential witness までまとめた stage-7 handoff。

数値 mountain lower bound は `C,A` を explicit にした時点で
`mountainCount_gt_of_binaryCertificate` へ有限計算を渡せばよい。
-/
theorem exists_polynomialMountainLowerData
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ P : PolynomialStartBoundData D,
      ∀ C : Word.MountainDecomposition D.word,
        Word.oddSteps D.word ≤
          P.binaryExponent * (2 ^ C.mountainCount - 1) := by
  obtain ⟨P⟩ := Z.exists_polynomialStartBoundData hPoly
  refine ⟨P, ?_⟩
  intro C
  exact D.oddSteps_le_binaryExponent_mul_mountainFactor P C

/--
Stage 5 の Barina--Hercher lower bound と stage 7 を同時に保持する handoff。

polynomial witness の具体定数が入った時点で、`72057431991 <= p` と
binary certificate を同じ packet で数値評価できる。
-/
theorem exists_largePolynomialMountainLowerData
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hPoly : External.TwoThreeGapPolynomialBound)
    (hBarina : External.BarinaTwoPow71Input)
    (hCF : External.HercherTwoPow71DenominatorInput) :
    ∃ P : PolynomialStartBoundData D,
      72057431991 ≤ Word.oddSteps D.word ∧
      ∀ C : Word.MountainDecomposition D.word,
        Word.oddSteps D.word ≤
          P.binaryExponent * (2 ^ C.mountainCount - 1) := by
  obtain ⟨P⟩ := Z.exists_polynomialStartBoundData hPoly
  refine ⟨P, D.oddSteps_ge_72057431991 hBarina hCF, ?_⟩
  intro C
  exact D.oddSteps_le_binaryExponent_mul_mountainFactor P C

/-- repository default Barina / continued-fraction inputs を使う convenience theorem。 -/
theorem exists_largePolynomialMountainLowerData_external
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ P : PolynomialStartBoundData D,
      72057431991 ≤ Word.oddSteps D.word ∧
      ∀ C : Word.MountainDecomposition D.word,
        Word.oddSteps D.word ≤
          P.binaryExponent * (2 ^ C.mountainCount - 1) :=
  CanonicalEndpointFloorContractingReturn.exists_largePolynomialMountainLowerData Z
    hPoly
    External.barinaTwoPow71
    External.hercherTwoPow71Denominator

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
