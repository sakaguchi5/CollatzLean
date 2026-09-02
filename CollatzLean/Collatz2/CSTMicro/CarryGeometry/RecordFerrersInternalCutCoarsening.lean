import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RecordFerrersGenericStartCoarsening

/-!
# RecordFerrers: record block 内部 cut の coarsening telescope

`D : RankRecordDecomposition w a` が覆う interval

  [a, a + D.lengths.sum)

を内部 offset `d` で

  [a, a+d) ++ [a+d, a+D.lengths.sum)

に分割する。

generic-start 4B は全 interval について

  L_whole = 3*kappa + L_record + Delta_record

を与える。一方、cell residual-lambda interval は隣接 interval に対して additive なので、
左 prefix を右辺へ移項すれば

  L_suffix - L_record - Delta_record
    = 3*kappa + E_left,

  E_left := - L_prefix

という exact な内部-cut telescope が得られる。

重要なのは `E_left` が単なる「差として後付け定義した余り」ではなく、
実際の Ferrers cell interval `[a,a+d)` の residual-lambda 総和そのもの（の符号反転）
であることである。
-/

namespace Collatz2
namespace Word

open CSTMicro

namespace RankRecordDecomposition

/--
開始 cut `a` から内部 cut `a+d` までに通過した cell residual-lambda が
suffix 側へ移るときの左端補正。

`d = 0` なら補正は零。`d > 0` では途中で切った区間の情報を保持する。

この量自体は `RankRecordDecomposition` には依存せず、

  E_left = -L[a,a+d)

という任意区間の量である。
`RankRecordDecomposition` が必要になるのは、この補正を record block 全体の
coarsening telescope と接続するときだけである。
-/
def internalCutLeftEndpointCorrectionZ
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a d : ℕ) : ℤ :=
  - (columnProfileResidualLambdaInterval H m h a d : ℤ)

@[simp] theorem internalCutLeftEndpointCorrectionZ_zero
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a : ℕ) :
    internalCutLeftEndpointCorrectionZ H m h a 0 = 0 := by
  simp [internalCutLeftEndpointCorrectionZ,
    columnProfileResidualLambdaInterval]

/--
**## Record block 内部 cut の exact coarsening telescope**

whole covered interval の 4B normal form

  L_whole = 3*kappa + L_record + Delta_record

を offset `d` で分割すると、suffix は

  L_suffix
    = 3*kappa + L_record + Delta_record + E_left

となる。

ここで

  E_left = -L[a,a+d)

は内部 cut によって残る genuine endpoint term。

`E_left` 自体は record decomposition に依存しないが、
この定理では `[a, a + D.lengths.sum)` が record block 全体であることを使うため、
`D : RankRecordDecomposition w a` が必要になる。
-/
theorem cellResidualLambdaInternalCut_eq_three_mul_kappa_add_record_add_defect_add_endpoint
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    {d kappa : ℕ}
    (hd : d ≤ D.lengths.sum)
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa) :
    (columnProfileResidualLambdaInterval
        H (oddSteps w) h (a + d) (D.lengths.sum - d) : ℤ) =
      3 * (kappa : ℤ) +
        (D.profileBlockResidualLambdaSumFrom H h : ℤ) +
        D.profileLambdaCoarseningDefectZFrom H h +
        internalCutLeftEndpointCorrectionZ
          H (oddSteps w) h a d := by
  have hWhole :=
    D.cellResidualLambdaInterval_eq_three_mul_kappa_add_recordResidualLambdaFrom_add_defect
      H h hA
  have hSplitNat :=
    columnProfileResidualLambdaInterval_add
      H (oddSteps w) h a d (D.lengths.sum - d)
  have hLen : d + (D.lengths.sum - d) = D.lengths.sum := by
    omega
  rw [hLen] at hSplitNat
  have hSplitZ := congrArg (fun n : ℕ => (n : ℤ)) hSplitNat
  push_cast at hSplitZ
  unfold internalCutLeftEndpointCorrectionZ
  linarith

/--
同じ内容を「suffix 側の coarsening residual」という差の形で読む wrapper。

  R_partial := L_suffix - L_record - Delta_record
             = 3*kappa + E_left.

ここでも `E_left` は record decomposition 自体の量ではなく、
開始 cut `a` から内部 cut `a+d` までの区間だけで決まる。
-/
theorem internalCutCoarseningResidual_eq_three_mul_add_endpoint
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    {d kappa : ℕ}
    (hd : d ≤ D.lengths.sum)
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa) :
    (columnProfileResidualLambdaInterval
        H (oddSteps w) h (a + d) (D.lengths.sum - d) : ℤ) -
        (D.profileBlockResidualLambdaSumFrom H h : ℤ) -
        D.profileLambdaCoarseningDefectZFrom H h =
      3 * (kappa : ℤ) +
        internalCutLeftEndpointCorrectionZ
          H (oddSteps w) h a d := by
  have hMain :=
    D.cellResidualLambdaInternalCut_eq_three_mul_kappa_add_record_add_defect_add_endpoint
      H h hd hA
  linarith

end RankRecordDecomposition
end Word
end Collatz2
