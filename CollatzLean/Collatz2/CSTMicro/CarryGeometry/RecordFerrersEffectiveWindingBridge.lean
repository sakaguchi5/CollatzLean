import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RecordFerrersResidualCoarsening
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RankTopChainWindingLedger

/-!
# RecordFerrers 4B: residual lambda と有効 winding の block 化

4A では final profile の raw cell cost を record block ごとにまとめ、

  A_record = A(h) + kappa,
  R(h) = G * kappa + R_record,
  R_record < G * (#records)

まで得た。

4B では rank-top winding 側を同じ record block 座標へ移す。

まず actual Ferrers chain では

  lambdaSum = 3 * A + L

なので、既存の rank-top winding telescope

  nB = jA + lambdaSum - 3 * carryCount

と

  E = carryCount - A

を合わせると exact に

  3 * E = jA + L - nB

となる。

次に record block の raw cost `C_b` 自身に residual lambda を適用し、

  L_record = sum_b residualLambda(G, C_b)

を定義する。各 block residual lambda は `{0,1,2,3}` なので

  L_record <= 3 * (#records)

は無条件に成り立つ。

ただし cell-level `L(h)` と block-level `L_record` は一般には同じではない。
4A の `kappa` を使って、その差を signed defect

  Delta_record
    = (3*A(h)+L(h)) - (3*A_record+L_record)

として exact に保持する。このとき

  L(h) = 3*kappa + L_record + Delta_record

であり、record 有効 winding

  E_record = E - kappa

について

  3 * E_record
    = jA + L_record + Delta_record - nB

を得る。

従って 4B の genuinely new な残課題は `Delta_record` の RecordFerrers 固有上界である。
任意の block 化では `Delta_record <= 0` 等は成立しないため、このファイルでは
そのような仮定を置かない。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

/-! ## 1. chain-level の residualized winding identity -/

namespace FerrersChain

/--
chain 全体の rank-top lambda sum は
full-gap quotient sum と residual lambda sum に exact 分解する。

  Lambda = 3*A + L.
-/
theorem rankTopLambdaSum_eq_three_mul_costQuotientSum_add_residualLambdaSum
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C.rankTopLambdaSum =
      3 * C.actualCostQuotientSum + C.actualResidualLambdaSum := by
  induction C with
  | refl =>
      simp [rankTopLambdaSum, actualCostQuotientSum, actualResidualLambdaSum]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hStep :=
        S.actualRankTopLambda_eq_three_mul_costQuotient_add_residualLambda
          hUFP
      change
        C.rankTopLambdaSum + S.actualRankTopLambda =
          3 * (C.actualCostQuotientSum + S.actualRankTopCostQuotient) +
            (C.actualResidualLambdaSum + S.actualResidualRankTopLambda)
      rw [ih, hStep]
      omega

end FerrersChain

namespace FirstFailureProvenance

/--
first-failure provenance の rank-top winding を residualized 座標へ直した exact normal form。

  3 * E = jA + L - nB.

ここで

* `E` は boundary -> upper chain の actual effective winding sum,
* `L` は同 chain の residual lambda sum,
* `jA` は boundary numerator の winding,
* `nB` は final first-failure winding。

carry count と full-gap quotient は結論から完全に消える。
-/
theorem exists_residualizedRankTopWinding
    {target : ParityWord}
    (P : FirstFailureProvenance target)
    (hLen : 2 < P.upper.length) :
    ∃ nB : ℕ,
      1 ≤ nB ∧
      nB < Collatz2.Word.oddSteps P.toFirstFailureEdge.upperExponentWord ∧
      ∃ jA : ℤ,
        FerrersStep.parityRankTopNumerator
            P.boundary
            P.boundary_isBoundary.1
            (by
              have hC := P.boundaryToUpperRankTopChain.length_eq
              rw [hC]
              omega) =
          (wordTerminalGap P.boundary : ℤ) * jA
        ∧
        3 * P.boundaryToUpperRankTopChain.actualEffectiveWindingSum =
          jA +
            (P.boundaryToUpperRankTopChain.actualResidualLambdaSum : ℤ) -
            (nB : ℤ) := by
  obtain ⟨nB, hnPos, hnLt, jA, hBoundary, hTrace⟩ :=
    P.exists_rankTopWinding_with_boundary_trace hLen
  let C := P.boundaryToUpperRankTopChain
  have hLambdaNat :=
    C.rankTopLambdaSum_eq_three_mul_costQuotientSum_add_residualLambdaSum
      P.boundary_isBoundary.1
  have hLambda :
      (C.rankTopLambdaSum : ℤ) =
        3 * (C.actualCostQuotientSum : ℤ) +
          (C.actualResidualLambdaSum : ℤ) := by
    exact_mod_cast hLambdaNat
  have hEffective :=
    C.actualEffectiveWindingSum_eq_carryCount_sub_costQuotientSum
  have hTrace' := hTrace
  rw [
    boundaryToUpperLambdaTrace,
    boundaryToUpperCarryTrace,
    FerrersChain.rankTopLambdaTrace_sum_eq_rankTopLambdaSum,
    FerrersChain.rankTopCarryTrace_sum_eq_normalizedCarryCount
  ] at hTrace'
  have hE :
      C.actualEffectiveWindingSum =
        (C.normalizedCarryCount : ℤ) -
          (C.actualCostQuotientSum : ℤ) := by
    exact hEffective
  refine ⟨nB, hnPos, hnLt, jA, hBoundary, ?_⟩
  dsimp [C] at hLambda hE ⊢
  rw [hLambda] at hTrace'
  rw [hE]
  linarith

end FirstFailureProvenance

/-! ## 2. record block ごとの residual lambda -/

/--
block raw cost list に residual lambda を適用した総和。

各 block の raw cost を一つの大きな cell と見なし、
`G` による Euclid remainder 側の four-letter lambda だけを残す。
-/
def recordBlockResidualLambdaSum
    (G : ℕ)
    (costs : List ℕ) : ℕ :=
  (costs.map (fun C => residualRankTopLambda G C)).sum

/-- block raw cost list に full rank-top lambda を適用した総和。 -/
def recordBlockFullLambdaSum
    (G : ℕ)
    (costs : List ℕ) : ℕ :=
  (costs.map (fun C => rankTopLambda G C)).sum

/--
positive gap では一つの block residual lambda は `3` 以下。
-/
theorem residualRankTopLambda_le_three
    {G C : ℕ}
    (hG : 0 < G) :
    residualRankTopLambda G C ≤ 3 := by
  rcases residualRankTopLambda_cases (G := G) (C := C) hG with
    h0 | h1 | h2 | h3
  · omega
  · omega
  · omega
  · omega

/--
block residual lambda の総和は `3 * blockCount` 以下。
-/
theorem recordBlockResidualLambdaSum_le_three_mul_length
    {G : ℕ}
    (hG : 0 < G)
    (costs : List ℕ) :
    recordBlockResidualLambdaSum G costs ≤ 3 * costs.length := by
  induction costs with
  | nil =>
      simp [recordBlockResidualLambdaSum]
  | cons C costs ih =>
      have hC : residualRankTopLambda G C ≤ 3 :=
        residualRankTopLambda_le_three hG
      simp only [recordBlockResidualLambdaSum, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      omega

/--
block full lambda も quotient + residual lambda に exact 分解する。

  Lambda_record = 3*A_record + L_record.
-/
theorem recordBlockFullLambdaSum_eq_three_mul_quotientSum_add_residualLambdaSum
    {G : ℕ}
    (hG : 0 < G)
    (costs : List ℕ) :
    recordBlockFullLambdaSum G costs =
      3 * recordBlockCostQuotientSum G costs +
        recordBlockResidualLambdaSum G costs := by
  induction costs with
  | nil =>
      simp [recordBlockFullLambdaSum, recordBlockCostQuotientSum,
        recordBlockResidualLambdaSum]
  | cons C costs ih =>
      have hC :=
        rankTopLambda_eq_three_mul_quotient_add_residualLambda
          (G := G) (C := C) hG
      simp only [recordBlockFullLambdaSum, recordBlockCostQuotientSum,
        recordBlockResidualLambdaSum, List.map_cons, List.sum_cons] at ih ⊢
      rw [hC, ih]
      omega

namespace RankRecordDecomposition

/-- record block ごとの bounded residual lambda 総和 `L_record`。 -/
def profileBlockResidualLambdaSum
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockResidualLambdaSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCosts H h)

/-- record block ごとの full lambda 総和。 -/
def profileBlockFullLambdaSum
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockFullLambdaSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCosts H h)

/--
4B の無条件 record-count bound。

  L_record <= 3 * (#records).
-/
theorem profileBlockResidualLambdaSum_le_three_mul_recordCount
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    profileBlockResidualLambdaSum D H h ≤
      3 * D.profileRecordCount := by
  have h :=
    recordBlockResidualLambdaSum_le_three_mul_length
      hGap (D.profileBlockCosts H h)
  rw [D.profileBlockCosts_length H] at h
  simpa [profileBlockResidualLambdaSum] using h

/--
record block full lambda の exact decomposition。
-/
theorem profileBlockFullLambdaSum_eq_three_mul_recordQuotient_add_recordResidualLambda
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    profileBlockFullLambdaSum D H h =
      3 * D.profileBlockCostQuotientSum H h +
        profileBlockResidualLambdaSum D H h := by
  exact
    recordBlockFullLambdaSum_eq_three_mul_quotientSum_add_residualLambdaSum
      hGap (D.profileBlockCosts H h)

/--
cell-level full lambda normal form と block-level full lambda normal form の signed 差。

  Delta_record
    = (3*A(h)+L(h)) - (3*A_record+L_record).

任意 block 化では符号は固定されないので `Int` で保持する。
-/
def profileLambdaCoarseningDefectZ
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  3 *
      (columnProfileCostQuotientSum H (oddSteps w) h : ℤ) +
    (columnProfileResidualLambdaSum H (oddSteps w) h : ℤ) -
    (3 * (D.profileBlockCostQuotientSum H h : ℤ) +
      (profileBlockResidualLambdaSum D H h : ℤ))

/--
4A の quotient carry `kappa` を使うと、cell residual lambda は

  L(h) = 3*kappa + L_record + Delta_record

へ exact に分解される。
-/
theorem cellResidualLambda_eq_three_mul_kappa_add_recordResidualLambda_add_defect
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSum H h =
        columnProfileCostQuotientSum H (oddSteps w) h + kappa) :
    (columnProfileResidualLambdaSum H (oddSteps w) h : ℤ) =
      3 * (kappa : ℤ) +
        (profileBlockResidualLambdaSum D H h : ℤ) +
        profileLambdaCoarseningDefectZ D H h := by
  unfold profileLambdaCoarseningDefectZ
  have hAZ := congrArg (fun n : ℕ => (n : ℤ)) hA
  push_cast at hAZ
  rw [hAZ]
  ring

/--
4A の `kappa` と 4B の lambda normal form を同時に返す checkpoint。
-/
theorem exists_recordLambdaCoarseningNormalForm
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    ∃ kappa : ℕ,
      D.profileBlockCostQuotientSum H h =
        columnProfileCostQuotientSum H (oddSteps w) h + kappa ∧
      columnProfileResidualCostSum H (oddSteps w) h =
        columnLayerGap H (oddSteps w) * kappa +
          D.profileBlockResidualCostSum H h ∧
      (columnProfileResidualLambdaSum H (oddSteps w) h : ℤ) =
        3 * (kappa : ℤ) +
          (profileBlockResidualLambdaSum D H h : ℤ) +
          profileLambdaCoarseningDefectZ D H h := by
  obtain ⟨kappa, hA, hR⟩ := D.exists_recordCoarseningCarry H h hGap
  refine ⟨kappa, hA, hR, ?_⟩
  exact
    cellResidualLambda_eq_three_mul_kappa_add_recordResidualLambda_add_defect
     D H h hA

end RankRecordDecomposition

/-! ## 3. record 有効 winding への exact rewrite -/

/--
cell-level residualized winding と 4A/4B の coarsening identity から、
record-level effective winding を得る純整数補題。

  3*E = jA + L - nB,
  L = 3*kappa + L_record + Delta

なら

  3*(E-kappa) = jA + L_record + Delta - nB.
-/
theorem recordEffectiveWinding_rewrite
    {E jA L nB kappa Lrecord delta : ℤ}
    (hCell : 3 * E = jA + L - nB)
    (hLambda : L = 3 * kappa + Lrecord + delta) :
    3 * (E - kappa) =
      jA + Lrecord + delta - nB := by
  linarith

/--
`nB >= 1` と `L_record <= 3*s` を入れた record-count upper bound。

残る未制御量は `Delta_record` のみ。
-/
theorem three_mul_recordEffectiveWinding_le_boundary_add_three_mul_records_add_defect_sub_one
    {Erecord jA Lrecord delta nB s : ℤ}
    (hEq :
      3 * Erecord = jA + Lrecord + delta - nB)
    (hnB : 1 ≤ nB)
    (hLrecord : Lrecord ≤ 3 * s) :
    3 * Erecord ≤
      jA + 3 * s + delta - 1 := by
  linarith

/--
`Delta_record <= Dmax` まで得られた場合の使いやすい wrapper。

将来 RecordFerrers 固有の幾何で `Dmax` を record 数や terminal data から
抑える theorem を証明すれば、そのまま global winding bound へ接続できる。
-/
theorem three_mul_recordEffectiveWinding_le_of_defectBound
    {Erecord jA Lrecord delta nB s Dmax : ℤ}
    (hEq :
      3 * Erecord = jA + Lrecord + delta - nB)
    (hnB : 1 ≤ nB)
    (hLrecord : Lrecord ≤ 3 * s)
    (hDelta : delta ≤ Dmax) :
    3 * Erecord ≤
      jA + 3 * s + Dmax - 1 := by
  linarith

end CSTMicro
end Collatz2
