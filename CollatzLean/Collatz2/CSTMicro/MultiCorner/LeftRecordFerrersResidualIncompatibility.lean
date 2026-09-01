import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RecordFerrersGenericStartCoarsening
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftExposedCriticalizationDigitBridge

/-!
# Left Case II: RecordFerrers coarsening residual と境界 digit の不両立

generic-start RecordFerrers coarsening の lambda normal form は

  L_interval = 3 * kappa + L_record + Delta_record

である。従って coarsening によって生じた補正部分

  R_coarse := L_interval - L_record - Delta_record

は exact に `3 * kappa` であり、mod 3 では必ず零になる。

一方、criticalization より左の canonical residual は 3-adic unit であり、
その mod 3 class は nonzero boundary digit を復号する。従って left residual を
`R_coarse` と同定することはできない。

注意すべき点は、`L_record` 自身が 3 の倍数なのではないことである。
four-letter residual lambda は一般に `0,1,2,3` を取り得る。3 の倍数になるのは、
signed defect まで差し引いた coarsening 補正部分そのものである。
-/

namespace Collatz2
namespace Word

open CSTMicro

namespace RankRecordDecomposition

/--
generic-start lambda coarsening で interval 側に残る補正 residual。

`L_interval` から block residual `L_record` と signed defect `Delta_record` を
差し引く。coarsening normal form により、これは後で exact に `3 * kappa` になる。
-/
def lambdaCoarseningCarryResidualZFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  (columnProfileResidualLambdaInterval
      H (oddSteps w) h a D.lengths.sum : ℤ) -
    (D.profileBlockResidualLambdaSumFrom H h : ℤ) -
    D.profileLambdaCoarseningDefectZFrom H h

/--
coarsening 補正 residual は quotient carry のちょうど3倍。
-/
theorem lambdaCoarseningCarryResidualZFrom_eq_three_mul
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa) :
    D.lambdaCoarseningCarryResidualZFrom H h =
      3 * (kappa : ℤ) := by
  have hLambda :=
    D.cellResidualLambdaInterval_eq_three_mul_kappa_add_recordResidualLambdaFrom_add_defect
      H h hA
  unfold lambdaCoarseningCarryResidualZFrom
  linarith

/--
従って coarsening 補正 residual は必ず3で割れる。
-/
theorem three_dvd_lambdaCoarseningCarryResidualZFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa) :
    (3 : ℤ) ∣ D.lambdaCoarseningCarryResidualZFrom H h := by
  refine ⟨(kappa : ℤ), ?_⟩
  exact D.lambdaCoarseningCarryResidualZFrom_eq_three_mul H h hA

/--
coarsening 補正 residual の `ZMod 3` digit は零。
-/
theorem lambdaCoarseningCarryResidualZFrom_mod_three_eq_zero
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa) :
    ((D.lambdaCoarseningCarryResidualZFrom H h : ℤ) : ZMod 3) = 0 := by
  exact
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (D.lambdaCoarseningCarryResidualZFrom H h) 3).2
      (D.three_dvd_lambdaCoarseningCarryResidualZFrom H h hA)

end RankRecordDecomposition
end Word

namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic
open Collatz2.Word

namespace LeftOfCriticalizationBridge

/--
left residual は、同じ cut から始めた RecordFerrers coarsening の
carry residual と一致できない。

前者は 3-adic unit、後者は exact に `3 * kappa` だからである。
-/
theorem leftResidual_ne_lambdaCoarseningCarryResidualZFrom
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P)
    {w : Word}
    (D : RankRecordDecomposition w B.left.index)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h B.left.index D.lengths.sum +
          kappa) :
    B.leftResidual ≠
      D.lambdaCoarseningCarryResidualZFrom H h := by
  intro hEq
  apply B.leftResidual_not_three_dvd
  rw [hEq]
  exact D.three_dvd_lambdaCoarseningCarryResidualZFrom H h hA

/--
境界 digit は、coarsening carry residual から作った digit と一致できない。

右辺は mod 3 で零だが、criticalization boundary digit は非零である。
-/
theorem boundaryDigit_ne_coarseningCarryResidualDigit
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P)
    {w : Word}
    (D : RankRecordDecomposition w B.left.index)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h B.left.index D.lengths.sum +
          kappa) :
    criticalizationBoundaryDigit P B.hStart ≠
      ((- (2 : ℤ) ^ beattyIndex B.left.index *
          D.lambdaCoarseningCarryResidualZFrom H h : ℤ) : ZMod 3) := by
  have hRightDvd :
      (3 : ℤ) ∣
        - (2 : ℤ) ^ beattyIndex B.left.index *
          D.lambdaCoarseningCarryResidualZFrom H h :=
    dvd_mul_of_dvd_right
      (D.three_dvd_lambdaCoarseningCarryResidualZFrom H h hA) _
  have hRightZero :
      ((- (2 : ℤ) ^ beattyIndex B.left.index *
          D.lambdaCoarseningCarryResidualZFrom H h : ℤ) : ZMod 3) = 0 := by
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (- (2 : ℤ) ^ beattyIndex B.left.index *
          D.lambdaCoarseningCarryResidualZFrom H h) 3).2 hRightDvd
  rw [hRightZero]
  exact criticalizationBoundaryDigit_ne_zero P B.hStart

/--
Case II の残る同定式が得られれば、直ちに矛盾へ落とせる最終 wrapper。

この theorem の仮定 `hIdentify` が、区間 Ferrers exact bridge と actual
RecordFerrers factorization から今後供給すべき唯一の接続式である。
-/
theorem false_of_leftResidual_eq_lambdaCoarseningCarryResidualZFrom
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P)
    {w : Word}
    (D : RankRecordDecomposition w B.left.index)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h B.left.index D.lengths.sum +
          kappa)
    (hIdentify :
      B.leftResidual =
        D.lambdaCoarseningCarryResidualZFrom H h) :
    False := by
  exact
    B.leftResidual_ne_lambdaCoarseningCarryResidualZFrom
      D H h hA hIdentify

end LeftOfCriticalizationBridge

end MultiCorner
end CSTMicro
end Collatz2
