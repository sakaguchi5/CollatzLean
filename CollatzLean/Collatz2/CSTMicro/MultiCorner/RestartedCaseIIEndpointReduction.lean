import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalAffineNumerator
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSharedCostTwoBand

namespace Collatz2
namespace CSTMicro

open  ExternalArithmetic

namespace MultiCorner

namespace RestartedTerminalGeometryPacket

/--
Case II の endpoint branch `s = c` に残る exact arithmetic bridge。

ここでは未証明の内容を隠さない。
必要なのは、Shared-Cost 側の二重 normalized defect 候補が、
restarted affine seed の正の整数倍として exact に現れることだけである。

この bridge が actual endpoint state の quotient から導ければ、
二帯域不等式は直ちに閉じる。
-/
def CaseIIEndpointAffineSharedCostBridge
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (A : AttachedSharedCostPair)
    (D0 D1 : ℤ) : Prop :=
  P.criticalizationStart = P.terminalCriticalStart ∧
    ∃ K : ℤ,
      0 < K ∧
        A.modulus * A.doubleNormalizedQCandidate D0 D1 =
          K * (S.affineSeed : ℤ)

/--
endpoint exact bridge があれば、二重 normalized defect 候補は strict positive。

ここでは first-passage legality を一切仮定しない。
したがって算術側と幾何側を分離した reduction になっている。
-/
theorem doubleNormalizedQCandidate_pos_of_caseIIEndpointBridge
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (A : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hBridge : S.CaseIIEndpointAffineSharedCostBridge A D0 D1) :
    0 < A.doubleNormalizedQCandidate D0 D1 := by
  rcases hBridge with ⟨_hsEq, K, hK, hExact⟩
  have hSeedNat : 0 < S.affineSeed :=
    S.affineSeed_pos
  have hSeed : (0 : ℤ) < (S.affineSeed : ℤ) := by
    exact_mod_cast hSeedNat
  have hRight :
      0 < K * (S.affineSeed : ℤ) :=
    mul_pos hK hSeed
  have hLeft :
      0 < A.modulus * A.doubleNormalizedQCandidate D0 D1 := by
    rw [hExact]
    exact hRight
  nlinarith [A.modulus_pos]

/--
Case II endpoint bridge から strict two-band bound を直接得る。

`D0 + D1 < gap + normalizedQ`
なので、元の目標 `(R)` の non-strict 版より強い。
-/
theorem defectSum_lt_gap_add_normalizedQ_of_caseIIEndpointBridge
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (A : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hBridge : S.CaseIIEndpointAffineSharedCostBridge A D0 D1) :
    D0 + D1 < A.gap + A.normalizedQ := by
  have hPos :=
    S.doubleNormalizedQCandidate_pos_of_caseIIEndpointBridge
      A D0 D1 hBridge
  unfold AttachedSharedCostPair.doubleNormalizedQCandidate at hPos
  linarith

/--
Case II endpoint bridge から元の two-band inequality `(R)` を得る wrapper。
-/
theorem defectSum_le_gap_add_normalizedQ_of_caseIIEndpointBridge
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (A : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hBridge : S.CaseIIEndpointAffineSharedCostBridge A D0 D1) :
    D0 + D1 ≤ A.gap + A.normalizedQ := by
  exact le_of_lt
    (S.defectSum_lt_gap_add_normalizedQ_of_caseIIEndpointBridge
      A D0 D1 hBridge)

end RestartedTerminalGeometryPacket

end MultiCorner
end CSTMicro
end Collatz2
