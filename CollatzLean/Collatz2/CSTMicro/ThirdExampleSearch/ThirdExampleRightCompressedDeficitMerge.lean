import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDecoderIndependentProfileBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleD3CleanAggregate
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.MaximalHorizontalBandCoarsening

/-!
# 第3例探索 8: 右 `3^42` compressed deficit evaluator との合流

actual unit-cell Ferrers 表現を hot path で展開しないため、既存の
`MaximalHorizontalBandCover` を圧縮 representation として使う。

各 compressed band の shifted-Phi weight を `mod 3^42` で返す evaluator を
interface として切り出し、その list fold が actual Ferrers deficit の右 residue と
exact に一致することを証明する。

最後に clean D3 の

  thirdExampleCleanEndpointResidueOfDeficit

へその residue を直接渡し、Case II / Last41 を経由せず actual endpoint residue へ合流する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/--
一つの compressed Ferrers band を右 modulus 上で評価する hot-path interface。
実装は後から Ostrowski/Christoffel block evaluator に差し替えられる。
-/
structure ThirdExampleRightBandEvaluator where
  eval : FerrersRowBand → ZMod thirdExampleRightModulus
  exact : ∀ b : FerrersRowBand,
    eval b =
      (rowBandPhiWeight thirdExampleTargetP b : ZMod thirdExampleRightModulus)

/-- compressed band list の右 residue fold。 -/
def thirdExampleRightCompressedDeficit
    (E : ThirdExampleRightBandEvaluator) :
    List FerrersRowBand → ZMod thirdExampleRightModulus
  | [] => 0
  | b :: bs => E.eval b + thirdExampleRightCompressedDeficit E bs

/-- evaluator certificate があれば list fold は shifted-Phi 総和の cast に一致する。 -/
theorem thirdExampleRightCompressedDeficit_exact_list
    (E : ThirdExampleRightBandEvaluator)
    (bands : List FerrersRowBand) :
    thirdExampleRightCompressedDeficit E bands =
      (rowBandPhiSum thirdExampleTargetP bands : ZMod thirdExampleRightModulus) := by
  induction bands with
  | nil =>
      simp [thirdExampleRightCompressedDeficit, rowBandPhiSum]
  | cons b bs ih =>
      simp only [thirdExampleRightCompressedDeficit, rowBandPhiSum]
      rw [E.exact b, ih]
      push_cast
      rfl

/--
maximal horizontal band cover を使った compressed evaluator は actual Ferrers deficit と一致する。
-/
theorem thirdExampleRightCompressedDeficit_exact_actual
    (E : ThirdExampleRightBandEvaluator)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (Cover : MaximalHorizontalBandCover w) :
    thirdExampleRightCompressedDeficit E (maximalHorizontalBands Cover) =
      (deficit : ZMod thirdExampleRightModulus) := by
  rw [thirdExampleRightCompressedDeficit_exact_list]
  have hCoarse := actualFerrersBands_eq_maximalHorizontalBands_phi Cover
  rw [C.oddSteps_eq] at hCoarse
  have hDef := cleanExactCriticalGapOne_deficit_eq_actualFerrersDeficitZ C
  have hActualPhi :
      rowBandPhiSum thirdExampleTargetP (actualFerrersBands w) =
        (deficit : ℤ) := by
    rw [← integerFerrersDeficit_eq_rowBandPhiSum]
    exact hDef.symm
  have hCompressedPhi :
      rowBandPhiSum thirdExampleTargetP (maximalHorizontalBands Cover) =
        (deficit : ℤ) := by
    rw [← hCoarse]
    exact hActualPhi
  have hCast := congrArg
    (fun z : ℤ => (z : ZMod thirdExampleRightModulus))
    hCompressedPhi
  simpa using hCast

/--
compressed right evaluator を clean D3 endpoint 復元器へ直接合流する中心 theorem。
-/
theorem thirdExampleRightCompressedEndpoint_exact
    (E : ThirdExampleRightBandEvaluator)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (Cover : MaximalHorizontalBandCover w) :
    thirdExampleCleanEndpointResidueOfDeficit
        (thirdExampleRightCompressedDeficit E
          (maximalHorizontalBands Cover)) =
      (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
  rw [thirdExampleRightCompressedDeficit_exact_actual E C Cover]
  exact thirdExampleCleanEndpointResidueOfDeficit_exact CertR C

/--
range certificate により endpoint が `3^42` 未満なら、上の右 residue の canonical
Nat representative は actual endpoint 整数そのものになる。
-/
theorem thirdExampleRightCompressedEndpoint_val_exact
    (R : ThirdExampleRangeCertificate)
    (E : ThirdExampleRightBandEvaluator)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (Cover : MaximalHorizontalBandCover w) :
    (thirdExampleCleanEndpointResidueOfDeficit
        (thirdExampleRightCompressedDeficit E
          (maximalHorizontalBands Cover))).val =
      gapOneEndpointValue m := by
  let : NeZero thirdExampleRightModulus :=
    ⟨Nat.ne_of_gt thirdExampleRightModulus_pos⟩
  have hEq := thirdExampleRightCompressedEndpoint_exact E CertR C Cover
  have hVal := congrArg ZMod.val hEq
  have hLt := thirdExampleEndpoint_lt_threePow42 R C
  simpa [Nat.mod_eq_of_lt hLt] using hVal

end ThirdExampleSearch
end CSTMicro
end Collatz2
