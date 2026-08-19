import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileDefectBridge

/-!
# Pure B profile block reduction

Stage 5 では minimal bad word `B` から actual history を消去し、pure packet

  Ψ(m) - N(h) - G*y = 3^m*q,
  H = beattyIndex(m) + 1,
  3*q < m

を得た。

このファイルでは、その deep equation を Stage 3/4 の phase-aware block calculus へ
完全に移す。

まず terminal gap

  G = 2^H - 3^m

と critical-prefix gap

  Γ_m = 2^beattyIndex(m) - 3^m

の差が exact に一つの dyadic term

  G = Γ_m + 2^beattyIndex(m)

であることを使う。従って Stage 5 equation は

  criticalPrefixDefectZ(m,y)
    = N(h) + 2^beattyIndex(m) * y + 3^m*q

へ変形される。

さらに Stage 4 の exact fold

  criticalPrefixDefectZ(m,y)
    = actualCriticalPhaseDefectFold 0 blocks(m) y

を代入し、global phase balance を得る。

profile numerator `N(h)` 側では既存 level-set decomposition と canonical maximal
interval decomposition を保持する。各 maximal interval `[a,b)` については

  2^(j+1) C_j[a,b]
    = 3^(m-b) Ψ(b) - 3^(m-a) Ψ(a)

の両 endpoint `Ψ(a), Ψ(b)` を、それぞれ actual Ostrowski phase-defect fold と
prefix gap に exact に展開する。

この段階では shifted block を長さだけから raw/corrected Christoffel block と同一視しない。
Stage 7 はここで得る finite phase geometry から right-end 3-adic collision を抽出する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-! ## 1. critical prefix value as phase fold + gap term -/

/--
critical prefix `Ψ(n)` を Stage 4 phase-defect fold と prefix-gap term に分けた値。
-/
def criticalPrefixPhaseValue
    (n : ℕ)
    (y : ℤ) : ℤ :=
  actualCriticalPhaseDefectFold
      0 (actualCriticalOstrowskiBlockScales n) y +
    criticalPrefixGapZ n * y

/-- phase value は critical prefix numerator `Ψ(n)` そのもの。 -/
theorem criticalPrefixPhaseValue_eq_criticalPrefixPhiZ
    (n : ℕ)
    (y : ℤ) :
    criticalPrefixPhaseValue n y = criticalPrefixPhiZ n := by
  unfold criticalPrefixPhaseValue
  rw [← criticalPrefixDefectZ_eq_actualOstrowskiPhaseDefectFold]
  unfold criticalPrefixDefectZ
  ring

/-- endpoint form を逆向きでも使うための wrapper。 -/
theorem criticalPrefixPhiZ_eq_criticalPrefixPhaseValue
    (n : ℕ)
    (y : ℤ) :
    criticalPrefixPhiZ n = criticalPrefixPhaseValue n y := by
  exact (criticalPrefixPhaseValue_eq_criticalPrefixPhiZ n y).symm

/-! ## 2. terminal gap = critical gap + one dyadic correction -/

namespace PureBProfileObstruction

/-- terminal correction `2^beattyIndex(m) * y`。 -/
def terminalDyadicCorrection
    (P : PureBProfileObstruction) : ℤ :=
  (2 : ℤ) ^ beattyIndex P.m * P.y

/--
`H = beattyIndex(m)+1` により terminal gap は critical-prefix gap より
exact に `2^beattyIndex(m)` だけ大きい。
-/
theorem gap_cast_eq_criticalPrefixGapZ_add_twoPow
    (P : PureBProfileObstruction) :
    (P.gap : ℤ) =
      criticalPrefixGapZ P.m +
        (2 : ℤ) ^ beattyIndex P.m := by
  have hGapPos :
      0 < 2 ^ P.H - 3 ^ P.m := by
    simpa [PureBProfileObstruction.gap, columnLayerGap] using P.gap_pos
  have hPowLt : 3 ^ P.m < 2 ^ P.H :=
    Nat.sub_pos_iff_lt.mp hGapPos
  have hGapNat :
      P.gap + 3 ^ P.m = 2 ^ P.H := by
    unfold PureBProfileObstruction.gap columnLayerGap
    exact Nat.sub_add_cancel (Nat.le_of_lt hPowLt)
  have hGapZ := congrArg (fun n : ℕ => (n : ℤ)) hGapNat
  push_cast at hGapZ
  calc
    (P.gap : ℤ)
        = (2 : ℤ) ^ P.H - (3 : ℤ) ^ P.m := by
            linarith
    _ =
        criticalPrefixGapZ P.m +
          (2 : ℤ) ^ beattyIndex P.m := by
            rw [P.terminal_beatty]
            unfold criticalPrefixGapZ
            rw [pow_succ]
            ring

/--
Stage 5 deep equation を critical-prefix defect へ移す中心 identity。
-/
theorem criticalPrefixDefectZ_eq_profile_add_terminal_add_deep
    (P : PureBProfileObstruction) :
    criticalPrefixDefectZ P.m P.y =
      (profileDyadicCellNumerator P.m P.h : ℤ) +
        P.terminalDyadicCorrection +
        (3 : ℤ) ^ P.m * (P.q : ℤ) := by
  have hGap := P.gap_cast_eq_criticalPrefixGapZ_add_twoPow
  have hGapColumn :
      (columnLayerGap P.H P.m : ℤ) =
        criticalPrefixGapZ P.m +
          (2 : ℤ) ^ beattyIndex P.m := by
    simpa [PureBProfileObstruction.gap] using hGap
  have hDeep := P.deep_profile_defect
  calc
    criticalPrefixDefectZ P.m P.y
        =
      (criticalPrefixPhiZ P.m -
          (profileDyadicCellNumerator P.m P.h : ℤ) -
          (columnLayerGap P.H P.m : ℤ) * P.y) +
        (profileDyadicCellNumerator P.m P.h : ℤ) +
        P.terminalDyadicCorrection := by
          unfold criticalPrefixDefectZ terminalDyadicCorrection
          rw [hGapColumn]
          ring
    _ =
      (3 : ℤ) ^ P.m * (P.q : ℤ) +
        (profileDyadicCellNumerator P.m P.h : ℤ) +
        P.terminalDyadicCorrection := by
          rw [hDeep]
    _ =
      (profileDyadicCellNumerator P.m P.h : ℤ) +
        P.terminalDyadicCorrection +
        (3 : ℤ) ^ P.m * (P.q : ℤ) := by
          ring

/--
Stage 4 fold を代入した global phase balance。
-/
theorem phaseDefectFold_eq_profile_add_terminal_add_deep
    (P : PureBProfileObstruction) :
    actualCriticalPhaseDefectFold
        0 (actualCriticalOstrowskiBlockScales P.m) P.y =
      (profileDyadicCellNumerator P.m P.h : ℤ) +
        P.terminalDyadicCorrection +
        (3 : ℤ) ^ P.m * (P.q : ℤ) := by
  calc
    actualCriticalPhaseDefectFold
        0 (actualCriticalOstrowskiBlockScales P.m) P.y
        = criticalPrefixDefectZ P.m P.y :=
          (criticalPrefixDefectZ_eq_actualOstrowskiPhaseDefectFold
            P.m P.y).symm
    _ =
      (profileDyadicCellNumerator P.m P.h : ℤ) +
        P.terminalDyadicCorrection +
        (3 : ℤ) ^ P.m * (P.q : ℤ) :=
          P.criticalPrefixDefectZ_eq_profile_add_terminal_add_deep

/--
phase fold から profile numerator と terminal dyadic correction を引いた residual。
Stage 7 が直接 3-adic valuation を読む global object。
-/
def phaseResidual
    (P : PureBProfileObstruction) : ℤ :=
  actualCriticalPhaseDefectFold
      0 (actualCriticalOstrowskiBlockScales P.m) P.y -
    (profileDyadicCellNumerator P.m P.h : ℤ) -
    P.terminalDyadicCorrection

/-- phase residual は exact に `3^m*q`。 -/
theorem phaseResidual_eq_threePow_mul_q
    (P : PureBProfileObstruction) :
    P.phaseResidual =
      (3 : ℤ) ^ P.m * (P.q : ℤ) := by
  unfold phaseResidual
  rw [P.phaseDefectFold_eq_profile_add_terminal_add_deep]
  ring

/-- 特に phase residual は `3^m` で割れる。 -/
theorem threePow_dvd_phaseResidual
    (P : PureBProfileObstruction) :
    (3 : ℤ) ^ P.m ∣ P.phaseResidual := by
  rw [P.phaseResidual_eq_threePow_mul_q]
  exact ⟨(P.q : ℤ), rfl⟩

/-! ## 3. profile side: levels and canonical maximal intervals -/

/-- profile numerator は既存 level-first numerator と exact に一致。 -/
theorem profileNumerator_eq_levelNumerator
    (P : PureBProfileObstruction) :
    profileDyadicCellNumerator P.m P.h =
      profileDyadicLevelNumerator P.m P.h :=
  profileDyadicCellNumerator_eq_levelNumerator P.admissible

/-- level numerator を finite sum の形で直接読む。 -/
theorem profileNumerator_eq_sum_layers
    (P : PureBProfileObstruction) :
    profileDyadicCellNumerator P.m P.h =
      Finset.sum (Finset.range (beattyIndex P.m))
        (fun j => profileDyadicLayerNumerator P.m P.h j) := by
  simpa [profileDyadicLevelNumerator] using P.profileNumerator_eq_levelNumerator

/-- layer `j` の canonical maximal interval decomposition。 -/
noncomputable def maximalLayerDecomposition
    (P : PureBProfileObstruction)
    (j : ℕ) :
    ProfileLayerIntervalDecomposition P.m P.h j :=
  maximalProfileLayerIntervalDecomposition P.m P.h j

/-- maximal decomposition は support cell を一意に覆う。 -/
theorem maximalLayer_cover_unique
    (P : PureBProfileObstruction)
    (j k : ℕ)
    (hk : k < P.m) :
    (j < P.h k ↔
      ∃! ab : ℕ × ℕ,
        ab ∈ maximalProfileLayerIntervals P.m P.h j ∧
          ab.1 ≤ k ∧ k < ab.2) := by
  have h :=
    (P.maximalLayerDecomposition j).cover_unique k hk
  change
    j < P.h k ↔
      ∃! ab : ℕ × ℕ,
        ab ∈ maximalProfileLayerIntervals P.m P.h j ∧
          ab.1 ≤ k ∧ k < ab.2 at h
  exact h

/-- fixed layer numerator は support 上の普通の cell sum。 -/
theorem layerNumerator_eq_supportSum
    (P : PureBProfileObstruction)
    (j : ℕ) :
    profileDyadicLayerNumerator P.m P.h j =
      Finset.sum (profileLayerSupport P.m P.h j)
        (fun k => profileDyadicCellTerm P.m k j) :=
  profileDyadicLayerNumerator_eq_supportSum P.m P.h j

/-! ## 4. every maximal interval is an endpoint Ostrowski phase difference -/

/--
maximal layer interval `[a,b)` の endpoint phase value。
-/
def maximalIntervalEndpointPhaseValue
    (P : PureBProfileObstruction)
    (ab : ℕ × ℕ) : ℤ :=
  (3 : ℤ) ^ (P.m - ab.2) *
      criticalPrefixPhaseValue ab.2 P.y -
    (3 : ℤ) ^ (P.m - ab.1) *
      criticalPrefixPhaseValue ab.1 P.y

/--
各 maximal interval の scaled numerator は、両 endpoint の canonical Ostrowski
phase values の差に exact 一致する。

`2^(j+1)` は 3-adic unit なので、Stage 7 ではこの式を valuation を失わず使える。
-/
theorem maximalInterval_scaledNumerator_eq_endpointPhaseValue
    (P : PureBProfileObstruction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals P.m P.h j) :
    (2 : ℤ) ^ (j + 1) *
        (profileDyadicIntervalNumerator
          P.m j ab.1 ab.2 : ℤ) =
      P.maximalIntervalEndpointPhaseValue ab := by
  have hEndpoint :=
    AdmissibleSturmianProfile.maximalLayerInterval_endpoint_prefix
      P.admissible hab
  unfold maximalIntervalEndpointPhaseValue
  simpa only [criticalPrefixPhaseValue_eq_criticalPrefixPhiZ] using hEndpoint

/-- maximal interval 自身の nonempty / inside / maximality summary。 -/
theorem maximalInterval_geometry
    (P : PureBProfileObstruction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals P.m P.h j) :
    ab.1 < ab.2 ∧
      ab.2 ≤ P.m ∧
      IsMaximalProfileLayerInterval P.m P.h j ab := by
  have hMem := mem_maximalProfileLayerIntervals_iff.mp hab
  exact ⟨hMem.2.2.1, hMem.2.1, hMem.2.2⟩

/--
maximal interval の left endpoint はその layer の genuine support cell。
-/
theorem maximalInterval_left_supported
    (P : PureBProfileObstruction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals P.m P.h j) :
    ab.1 ∈ profileLayerSupport P.m P.h j := by
  have hMax : IsMaximalProfileLayerInterval P.m P.h j ab :=
    (mem_maximalProfileLayerIntervals_iff.mp hab).2.2
  exact hMax.mem_support le_rfl hMax.1

/--
maximal interval の layer は left endpoint の Beatty roof より strict に下。
-/
theorem maximalInterval_layer_lt_leftBeatty
    (P : PureBProfileObstruction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals P.m P.h j) :
    j < beattyIndex ab.1 := by
  have hGeom := P.maximalInterval_geometry hab
  have haLtM : ab.1 < P.m := lt_of_lt_of_le hGeom.1 hGeom.2.1
  have hSupport := P.maximalInterval_left_supported hab
  have hLayer : j < P.h ab.1 :=
    (Finset.mem_filter.mp hSupport).2
  exact lt_of_lt_of_le hLayer (P.admissible.depth_le haLtM)

end PureBProfileObstruction

/-! ## 5. Stage-6 output packet -/

/--
Stage 7 が読む pure block-reduction packet。

Stage 5 の raw deep equationはここでは保持せず、既に Ostrowski phase fold へ変換された
`phase_balance` を core equation とする。
-/
structure PureBProfileBlockReduction where
  H : ℕ
  m : ℕ
  h : ℕ → ℕ
  q : ℕ
  y : ℤ

  admissible : AdmissibleSturmianProfile m h
  gap_pos : 0 < columnLayerGap H m
  one_lt_m : 1 < m
  terminal_beatty : H = beattyIndex m + 1
  small_strip : 3 * q < m

  phase_balance :
    actualCriticalPhaseDefectFold
        0 (actualCriticalOstrowskiBlockScales m) y =
      (profileDyadicCellNumerator m h : ℤ) +
        (2 : ℤ) ^ beattyIndex m * y +
        (3 : ℤ) ^ m * (q : ℤ)

namespace PureBProfileBlockReduction

/-- Stage-6 packet の phase residual。 -/
def phaseResidual
    (R : PureBProfileBlockReduction) : ℤ :=
  actualCriticalPhaseDefectFold
      0 (actualCriticalOstrowskiBlockScales R.m) R.y -
    (profileDyadicCellNumerator R.m R.h : ℤ) -
    (2 : ℤ) ^ beattyIndex R.m * R.y

/-- output packet でも residual は exact に `3^m*q`。 -/
theorem phaseResidual_eq_threePow_mul_q
    (R : PureBProfileBlockReduction) :
    R.phaseResidual =
      (3 : ℤ) ^ R.m * (R.q : ℤ) := by
  unfold phaseResidual
  rw [R.phase_balance]
  ring

/-- Stage 7 用の deep divisibility wrapper。 -/
theorem threePow_dvd_phaseResidual
    (R : PureBProfileBlockReduction) :
    (3 : ℤ) ^ R.m ∣ R.phaseResidual := by
  rw [R.phaseResidual_eq_threePow_mul_q]
  exact ⟨(R.q : ℤ), rfl⟩

/-- packet profile の maximal layer decomposition。 -/
noncomputable def maximalLayerDecomposition
    (R : PureBProfileBlockReduction)
    (j : ℕ) :
    ProfileLayerIntervalDecomposition R.m R.h j :=
  maximalProfileLayerIntervalDecomposition R.m R.h j

/-- output packet でも maximal interval endpoint phase formula を直接使える。 -/
theorem maximalInterval_scaledNumerator_eq_endpointPhaseValue
    (R : PureBProfileBlockReduction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals R.m R.h j) :
    (2 : ℤ) ^ (j + 1) *
        (profileDyadicIntervalNumerator
          R.m j ab.1 ab.2 : ℤ) =
      (3 : ℤ) ^ (R.m - ab.2) *
          criticalPrefixPhaseValue ab.2 R.y -
        (3 : ℤ) ^ (R.m - ab.1) *
          criticalPrefixPhaseValue ab.1 R.y := by
  have h :=
    AdmissibleSturmianProfile.maximalLayerInterval_endpoint_prefix
      R.admissible hab
  simpa only [criticalPrefixPhaseValue_eq_criticalPrefixPhiZ] using h

end PureBProfileBlockReduction

/-! ## 6. Stage 5 packet -> Stage 6 packet -/

namespace PureBProfileObstruction

/-- pure obstruction を Stage-6 block reduction へ送る。 -/
noncomputable def toProfileBlockReduction
    (P : PureBProfileObstruction) :
    PureBProfileBlockReduction := {
  H := P.H
  m := P.m
  h := P.h
  q := P.q
  y := P.y
  admissible := P.admissible
  gap_pos := P.gap_pos
  one_lt_m := P.one_lt_m
  terminal_beatty := P.terminal_beatty
  small_strip := P.small_strip
  phase_balance := P.phaseDefectFold_eq_profile_add_terminal_add_deep
}

@[simp] theorem toProfileBlockReduction_q
    (P : PureBProfileObstruction) :
    P.toProfileBlockReduction.q = P.q := by
  rfl

@[simp] theorem toProfileBlockReduction_m
    (P : PureBProfileObstruction) :
    P.toProfileBlockReduction.m = P.m := by
  rfl

end PureBProfileObstruction

namespace MinimalActualABObstructionPacket

/-- minimal actual B から Stage 6 pure block packet まで一気に送る。 -/
noncomputable def toPureBProfileBlockReduction
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    PureBProfileBlockReduction :=
  (M.toPureBProfileObstruction hL).toProfileBlockReduction

/-- Stage 6 packet の q は actual normalized q と同じ。 -/
theorem toPureBProfileBlockReduction_q_eq
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileBlockReduction hL).q = M.actual.q := by
  rfl

/--
Stage 7 boundary-fragment branch 用 companion。
Stage 6 packet の q は任意 first-passage predecessor residue より strict に小さい。
-/
theorem blockReductionQ_lt_predecessor_residue
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    ((M.toPureBProfileBlockReduction hL).q : ℤ) <
      S.edge.toFareyCellPacket.residue := by
  change
    ((M.toPureBProfileObstruction hL).q : ℤ) <
      S.edge.toFareyCellPacket.residue
  exact M.pureProfileQ_lt_predecessor_residue hL S hLowerFP

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
