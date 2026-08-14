import CollatzLean.Collatz2.Canonical.ZeroCoreCanonicalSlacks
import CollatzLean.Collatz2.Canonical.PrependOneSwapSeparation

/-!
# Collatz2 Canonical: true zero-core の swap/core-defect identity

true `j=0` canonical zero core に対し

  omega = prependOneSwapSeparation(v)
  G     = centerGap(1::v)
  T     = canonicalEnd(v)
  C     = 3^oddSteps(v)
  delta = coreDefect = 3*n

と置く。

exact に

  2*omega
    =
  G*(T+1) + 2*C*delta

が成立する。

従って counterexample packet では `delta > 0` なので

  G*(T+1) < 2*omega

が強制される。

今後 B を閉じるために必要な外側の唯一の数学は逆向き upper bound

  2*omega <= G*(T+1)

を endpoint-floor / canonical transport から示すこと。

このファイルではその未証明部分を仮定定数にせず Prop として切り出す。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn
namespace CanonicalZeroCoreData

open Word

/--
tail realization と natural coordinates から得る
swap separation の exact core-defect identity。
-/
theorem two_mul_swapSeparation_eq_gap_endpoint_add_coreDefect
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (L : Z.SlackData) :
    2 * Word.prependOneSwapSeparation Z.natural.tail =
      (AffineTransfer.ofWord (1 :: Z.natural.tail)).centerGap *
          (Word.canonicalEnd Z.natural.tail + 1) +
        2 * 3 ^ Word.oddSteps Z.natural.tail *
          L.coreDefect := by
  let v := Z.natural.tail
  let n := Z.natural.n
  let d := Z.natural.d
  let T := Word.canonicalEnd v
  let s := Word.canonicalStart v
  let A := 2 ^ Word.twoSteps v
  let C := 3 ^ Word.oddSteps v
  let B := Word.affineConst v
  let g := (AffineTransfer.ofWord v).centerGap
  let G := (AffineTransfer.ofWord (1 :: v)).centerGap
  have hTailC : Word.Contracting v :=
    Z.tail_contracting
  have hTailGap :
      g + C = A := by
    simpa [g, C, A] using hTailC.centerGap_add_threePow
  have hFullC :
      Word.Contracting (1 :: v) := by
    have h := D.contracting
    rw [Z.natural.word_eq] at h
    simpa [v] using h
  have hFullGap :
      G + 3 * C = 2 * A := by
    have h :=
      hFullC.centerGap_add_threePow
    simpa [G, C, A, Word.oddSteps, Word.twoSteps,
      pow_succ, pow_add,Nat.mul_comm] using h
  have hTwoG :
      G + C = 2 * g := by
    nlinarith [hTailGap, hFullGap]
  have hStart :
      s + 1 = 6 * (n + d) := by
    dsimp [s, n, d, v]
    rw [← Z.boundary_eq_tailStart]
    exact Z.natural.boundary_add_one
  have hEnd :
      T + 1 = 6 * n + 4 * d := by
    dsimp [T, n, d, v]
    rw [← Z.fullEnd_eq_tailEnd]
    exact Z.natural.fullEnd_add_one
  have hStartEnd :
      s = T + 2 * d := by
    omega
  have hReal' :
      A * T = C * s + B := by
    have h :=
      (Word.realizes_iff
        v
        (Word.canonicalStart v)
        (Word.canonicalEnd v)).1
        (Word.canonicalEnd_realizes v)
    simpa [A, T, C, s, B] using h
  have hRealGap :
      B + 2 * C * d = g * T := by
    rw [← hTailGap] at hReal'
    rw [hStartEnd] at hReal'
    ring_nf at hReal'
    nlinarith
  have hSep :
      Word.prependOneSwapSeparation v = B + g := by
    rfl
  have hTwoGMul :=
    congrArg (fun z : ℕ => z * (T + 1)) hTwoG
  have hCore :
      L.coreDefect = 3 * n := by
    rfl
  rw [hSep, hCore]
  dsimp [v, n, d, T, s, A, C, B, g, G] at *
  ring_nf at hRealGap hTwoGMul ⊢
  nlinarith

/-- core defect が正なので swap separation は endpoint half-bound を strict に越える。 -/
theorem gap_endpoint_lt_two_mul_swapSeparation
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (L : Z.SlackData) :
    (AffineTransfer.ofWord (1 :: Z.natural.tail)).centerGap *
        (Word.canonicalEnd Z.natural.tail + 1) <
      2 * Word.prependOneSwapSeparation Z.natural.tail := by
  have hEq :=
    Z.two_mul_swapSeparation_eq_gap_endpoint_add_coreDefect L
  have hDef := L.coreDefect_pos
  have hCpos :
      0 < 3 ^ Word.oddSteps Z.natural.tail :=
    Nat.pow_pos (by omega)
  have hExtra :
      0 <
        2 * 3 ^ Word.oddSteps Z.natural.tail *
          L.coreDefect :=
    Nat.mul_pos
      (Nat.mul_pos (by omega) hCpos)
      hDef
  omega

/--
B 排除の最後に必要な swap upper bound。
-/
def SwapCoreBound
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) : Prop :=
  2 * Word.prependOneSwapSeparation Z.natural.tail ≤
    (AffineTransfer.ofWord (1 :: Z.natural.tail)).centerGap *
      (Word.canonicalEnd Z.natural.tail + 1)

/--
現在の唯一の未証明数学を universal principle として命名する。
仮定定数ではなく単なる Prop。
-/
def CanonicalZeroCoreSwapPrinciple : Prop :=
  ∀ (O : OddOrbit)
    (D : CanonicalEndpointFloorContractingReturn O)
    (Z : CanonicalZeroCoreData D),
      Z.SwapCoreBound

/-- swap upper bound が得られれば true zero core は即矛盾。 -/
theorem false_of_swapCoreBound
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (L : Z.SlackData)
    (hBound : Z.SwapCoreBound) :
    False := by
  have hStrict :=
    Z.gap_endpoint_lt_two_mul_swapSeparation L
  exact (Nat.not_lt_of_ge hBound) hStrict

/-- universal swap principle があれば任意の true zero core は排除される。 -/
theorem false_of_swapPrinciple
    (hPrinciple : CanonicalZeroCoreSwapPrinciple)
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    False := by
  let L := Z.toSlackData
  exact Z.false_of_swapCoreBound L (hPrinciple O D Z)

end CanonicalZeroCoreData
end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
