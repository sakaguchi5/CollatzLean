import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect

/-!
# Actual Ostrowski phase-block decomposition

`CriticalPrefixOstrowski` は任意 prefix length を actual convergent numerators
`P_2,P_3,...` の bounded greedy Ostrowski digits へ分解した。

このファイルでは digits を実際の ordered interval blocks へ戻す。
重要なのは、shifted block を長さだけから Christoffel block と同一視しないことである。
各 block は

* left endpoint,
* continued-fraction scale,
* exact right endpoint,
* Beatty rise,
* interval numerator / gap / affine defect

をそのまま保持する。

origin block だけは既存 `beattyIndex = floor(i Q/P)` theorem から
Christoffel numerator と exact に同定する。shifted blocks は phase data を保持したまま
Stage 5 へ渡し、odd raw / even first-flat / boundary fragment の判定をそこで行う。

さらに block 列に沿う affine-defect fold を定義し、Stage 3 の concat law から
full prefix defect がその fold と exact に一致することを示す。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-! ## phase-aware single block -/

/-- actual Ostrowski decomposition の一つの scale block。 -/
structure ActualCriticalPhaseBlock where
  left : ℕ
  scale : ℕ

namespace ActualCriticalPhaseBlock

/-- block の standard scale length。 -/
def length
    (B : ActualCriticalPhaseBlock) : ℕ :=
  criticalPowerP B.scale

/-- block の right endpoint。 -/
def right
    (B : ActualCriticalPhaseBlock) : ℕ :=
  B.left + B.length

/-- block 内で増える Beatty exponent。これが shift/conjugacy phase を記録する。 -/
def betaRise
    (B : ActualCriticalPhaseBlock) : ℕ :=
  beattyIndex B.right - beattyIndex B.left

/-- block の exact interval numerator。 -/
def numerator
    (B : ActualCriticalPhaseBlock) : ℤ :=
  criticalIntervalPhiZ B.left B.right

/-- block の exact signed interval gap。 -/
def gap
    (B : ActualCriticalPhaseBlock) : ℤ :=
  criticalIntervalGapZ B.left B.right

/-- block の exact affine defect。 -/
def defect
    (B : ActualCriticalPhaseBlock)
    (y : ℤ) : ℤ :=
  criticalIntervalDefectZ B.left B.right y

@[simp] theorem right_eq
    (B : ActualCriticalPhaseBlock) :
    B.right = B.left + criticalPowerP B.scale := rfl

@[simp] theorem right_sub_left
    (B : ActualCriticalPhaseBlock) :
    B.right - B.left = criticalPowerP B.scale := by
  simp [right, length]

/-- scale が正なら block は nonempty。 -/
theorem left_lt_right
    (B : ActualCriticalPhaseBlock)
    (hScale : 1 ≤ B.scale) :
    B.left < B.right := by
  unfold right length
  have hP : 0 < criticalPowerP B.scale :=
    criticalPowerP_pos hScale
  omega

/--
shifted block が actual convergent `(P_r,Q_r)` の raw Christoffel phaseに exact に
aligned していること。長さだけではなく全 local Beatty exponents を要求する。
-/
def IsChristoffelAligned
    (B : ActualCriticalPhaseBlock) : Prop :=
  9 ≤ B.scale ∧
    ∀ i : ℕ,
      i < criticalPowerP B.scale →
      beattyIndex (B.left + i) - beattyIndex B.left =
        (i * criticalPowerQ B.scale) / criticalPowerP B.scale

end ActualCriticalPhaseBlock

/-- origin に置いた scale `r` block。 -/
def actualCriticalOriginPhaseBlock
    (r : ℕ) : ActualCriticalPhaseBlock :=
  ⟨0, r⟩

/-- origin block は start=9 以降 raw Christoffel phaseに aligned する。 -/
theorem actualCriticalOriginPhaseBlock_isChristoffelAligned
    {r : ℕ}
    (hr : 9 ≤ r) :
    (actualCriticalOriginPhaseBlock r).IsChristoffelAligned := by
  constructor
  · exact hr
  · intro i hi
    simp only [actualCriticalOriginPhaseBlock, zero_add, beattyIndex_zero, tsub_zero]
    exact actual_beattyIndex_eq_div hr hi

/-- `Ico a (a+n)` を local offset range へ移す。 -/
private theorem phase_sum_Ico_eq_sum_range
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    (a n : ℕ) :
    Finset.sum (Finset.Ico a (a + n)) f =
      Finset.sum (Finset.range n) (fun i => f (a + i)) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ hEq
    omega
  · intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    refine ⟨k - a, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro i hi
    rfl

/-- additive fold を finite sum へ移す local helper。 -/
private theorem foldl_range_add_eq_sum_phase
    (n : ℕ)
    (f : ℕ → ℤ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      Finset.sum (Finset.range n) f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [Finset.sum_range_succ, ih]

/-- Christoffel fold を finite sum として読む local wrapper。 -/
private theorem criticalChristoffelPhi_eq_sum_phase
    (p q : ℕ) :
    criticalChristoffelPhi p q =
      Finset.sum (Finset.range p)
        (fun i =>
          (3 : ℤ) ^ (p - 1 - i) *
            (2 : ℤ) ^ ((i * q) / p)) := by
  unfold criticalChristoffelPhi
  exact foldl_range_add_eq_sum_phase p
    (fun i =>
      (3 : ℤ) ^ (p - 1 - i) *
        (2 : ℤ) ^ ((i * q) / p))

/-- aligned phase block の numerator は actual Christoffel numerator。 -/
theorem ActualCriticalPhaseBlock.numerator_eq_christoffel_of_aligned
    (B : ActualCriticalPhaseBlock)
    (hAlign : B.IsChristoffelAligned) :
    B.numerator =
      criticalChristoffelPhi
        (criticalPowerP B.scale)
        (criticalPowerQ B.scale) := by
  rw [criticalChristoffelPhi_eq_sum_phase]
  unfold ActualCriticalPhaseBlock.numerator
    ActualCriticalPhaseBlock.right
    ActualCriticalPhaseBlock.length
    criticalIntervalPhiZ
  rw [phase_sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hiLt : i < criticalPowerP B.scale :=
    Finset.mem_range.mp hi
  have hPhase := hAlign.2 i hiLt
  have hThreeExp :
      B.left + criticalPowerP B.scale - 1 - (B.left + i) =
        criticalPowerP B.scale - 1 - i := by
    omega
  rw [hPhase, hThreeExp]
  ring

/-- origin block の numerator は existing `criticalChristoffelPhiAt` と exact に一致。 -/
theorem actualCriticalOriginPhaseBlock_numerator_eq_christoffelPhiAt
    {r : ℕ}
    (hr : 9 ≤ r) :
    (actualCriticalOriginPhaseBlock r).numerator =
      criticalChristoffelPhiAt actualCriticalContinuedFractionData r := by
  have hAlign := actualCriticalOriginPhaseBlock_isChristoffelAligned hr
  have hPhi :=
    ActualCriticalPhaseBlock.numerator_eq_christoffel_of_aligned
      (actualCriticalOriginPhaseBlock r) hAlign
  simpa [
    actualCriticalOriginPhaseBlock,
    criticalChristoffelPhiAt,
    actualCriticalContinuedFractionData
  ] using hPhi

/-! ## Ostrowski digits -> ordered scale blocks -/

namespace ActualCriticalOstrowskiExpansion

/--
Ostrowski digits を chronological low-to-high scale block list へ展開する。
base digit は `P_2=1` block、step digit `d` は scale `R+3` blockを `d` 個追加する。
-/
def blockScales :
    {R n : ℕ} →
      ActualCriticalOstrowskiExpansion R n → List ℕ
  | 0, _, .base n _ =>
      List.replicate n 2
  | R + 1, _, .step (d := d) lower _ _ _ _ =>
      blockScales lower ++ List.replicate d (R + 3)

end ActualCriticalOstrowskiExpansion

/-- scale list が覆う total prefix length。 -/
def actualCriticalBlockScaleMass
    (scales : List ℕ) : ℕ :=
  (scales.map criticalPowerP).sum

@[simp] theorem actualCriticalBlockScaleMass_nil :
    actualCriticalBlockScaleMass [] = 0 := by
  simp [actualCriticalBlockScaleMass]

@[simp] theorem actualCriticalBlockScaleMass_cons
    (r : ℕ)
    (rs : List ℕ) :
    actualCriticalBlockScaleMass (r :: rs) =
      criticalPowerP r + actualCriticalBlockScaleMass rs := by
  simp [actualCriticalBlockScaleMass]

@[simp] theorem actualCriticalBlockScaleMass_append
    (xs ys : List ℕ) :
    actualCriticalBlockScaleMass (xs ++ ys) =
      actualCriticalBlockScaleMass xs +
        actualCriticalBlockScaleMass ys := by
  simp [actualCriticalBlockScaleMass]

@[simp] theorem actualCriticalBlockScaleMass_replicate
    (d r : ℕ) :
    actualCriticalBlockScaleMass (List.replicate d r) =
      d * criticalPowerP r := by
  simp [actualCriticalBlockScaleMass]

/-- expansion の scale blocks は元の prefix length を exact に覆う。 -/
theorem ActualCriticalOstrowskiExpansion.blockScales_mass_eq
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) :
    actualCriticalBlockScaleMass E.blockScales = n := by
  induction E with
  | base n hBound =>
      have hP2 : criticalPowerP 2 = 1 := by
        norm_num [
          criticalPowerP,
          criticalPowerConvergent,
          criticalInitialConvergent
        ]
      simp [
        ActualCriticalOstrowskiExpansion.blockScales,
        actualCriticalBlockScaleMass,
        hP2
      ]
  | @step R n rem d lower hBound hDecomp hDigit hMax ih =>
      simp only [ActualCriticalOstrowskiExpansion.blockScales]
      rw [actualCriticalBlockScaleMass_append]
      rw [ih]
      rw [actualCriticalBlockScaleMass_replicate]
      exact hDecomp.symm

/-- bounded expansion を canonical choice として保持する。 -/
noncomputable def boundedActualCriticalOstrowskiExpansionChoice
    (R n : ℕ)
    (hn : n < criticalPowerP (R + 3)) :
    ActualCriticalOstrowskiExpansion R n :=
  Classical.choice (exists_actualCriticalOstrowskiExpansion R n hn)

/-- bounded canonical scale-block list。 -/
noncomputable def boundedActualCriticalOstrowskiBlockScales
    (R n : ℕ)
    (hn : n < criticalPowerP (R + 3)) : List ℕ :=
  (boundedActualCriticalOstrowskiExpansionChoice R n hn).blockScales

/-- bounded canonical block list は `n` を exact に覆う。 -/
theorem boundedActualCriticalOstrowskiBlockScales_mass_eq
    (R n : ℕ)
    (hn : n < criticalPowerP (R + 3)) :
    actualCriticalBlockScaleMass
        (boundedActualCriticalOstrowskiBlockScales R n hn) = n := by
  unfold boundedActualCriticalOstrowskiBlockScales
  exact
    ActualCriticalOstrowskiExpansion.blockScales_mass_eq
      (boundedActualCriticalOstrowskiExpansionChoice R n hn)

/-- arbitrary prefix `n` の canonical scale-block list。 -/
noncomputable def actualCriticalOstrowskiBlockScales
    (n : ℕ) : List ℕ :=
  boundedActualCriticalOstrowskiBlockScales n n
    (self_lt_criticalPowerP_add_three n)

/-- arbitrary canonical block list の total length は `n`。 -/
theorem actualCriticalOstrowskiBlockScales_mass_eq
    (n : ℕ) :
    actualCriticalBlockScaleMass
        (actualCriticalOstrowskiBlockScales n) = n := by
  unfold actualCriticalOstrowskiBlockScales
  exact
    boundedActualCriticalOstrowskiBlockScales_mass_eq
      n n (self_lt_criticalPowerP_add_three n)

/-! ## explicit ordered phase blocks -/

/-- scale list を left endpoint から consecutive phase blocks へ展開する。 -/
def actualCriticalPhaseBlocksFrom :
    ℕ → List ℕ → List ActualCriticalPhaseBlock
  | _, [] => []
  | left, r :: rs =>
      let B : ActualCriticalPhaseBlock := ⟨left, r⟩
      B :: actualCriticalPhaseBlocksFrom B.right rs

@[simp] theorem actualCriticalPhaseBlocksFrom_nil
    (left : ℕ) :
    actualCriticalPhaseBlocksFrom left [] = [] := rfl

@[simp] theorem actualCriticalPhaseBlocksFrom_cons
    (left r : ℕ)
    (rs : List ℕ) :
    actualCriticalPhaseBlocksFrom left (r :: rs) =
      let B : ActualCriticalPhaseBlock := ⟨left, r⟩
      B :: actualCriticalPhaseBlocksFrom B.right rs := rfl

/-- explicit block list は scale list と同じ個数を持つ。 -/
@[simp] theorem actualCriticalPhaseBlocksFrom_length
    (left : ℕ)
    (scales : List ℕ) :
    (actualCriticalPhaseBlocksFrom left scales).length = scales.length := by
  induction scales generalizing left with
  | nil => simp
  | cons r rs ih =>
      simp [actualCriticalPhaseBlocksFrom, ih]

/-- arbitrary prefix `n` の canonical phase-aware block list。 -/
noncomputable def actualCriticalOstrowskiPhaseBlocks
    (n : ℕ) : List ActualCriticalPhaseBlock :=
  actualCriticalPhaseBlocksFrom 0
    (actualCriticalOstrowskiBlockScales n)

/-! ## exact phase-block defect fold -/

/--
ordered scale blocks の affine defects を Stage 3 concat coefficients で fold する。
shifted phase は各 `criticalIntervalDefectZ left right` にそのまま残る。
-/
def actualCriticalPhaseDefectFold :
    ℕ → List ℕ → ℤ → ℤ
  | _, [], _ => 0
  | left, r :: rs, y =>
      let mid := left + criticalPowerP r
      (3 : ℤ) ^ actualCriticalBlockScaleMass rs *
          criticalIntervalDefectZ left mid y +
        (2 : ℤ) ^ (beattyIndex mid - beattyIndex left) *
          actualCriticalPhaseDefectFold mid rs y

/-- scale list の full interval defect は phase-block fold に exact に分解する。 -/
theorem criticalIntervalDefectZ_eq_phaseDefectFold
    (left : ℕ)
    (scales : List ℕ)
    (y : ℤ) :
    criticalIntervalDefectZ
        left
        (left + actualCriticalBlockScaleMass scales)
        y =
      actualCriticalPhaseDefectFold left scales y := by
  induction scales generalizing left with
  | nil =>
      simp [actualCriticalPhaseDefectFold]
  | cons r rs ih =>
      let mid := left + criticalPowerP r
      let finish := mid + actualCriticalBlockScaleMass rs
      have hLeftMid : left ≤ mid := by
        dsimp [mid]
        omega
      have hMidFinish : mid ≤ finish := by
        dsimp [finish]
        omega
      have hFinish :
          left + actualCriticalBlockScaleMass (r :: rs) = finish := by
        dsimp [finish, mid]
        simp [actualCriticalBlockScaleMass, Nat.add_assoc]
      have hTail := ih mid
      rw [hFinish]
      rw [criticalIntervalDefectZ_concat hLeftMid hMidFinish]
      have hExp : finish - mid = actualCriticalBlockScaleMass rs := by
        dsimp [finish]
        omega
      rw [hExp, hTail]
      rfl

/-- canonical Ostrowski blocks give an exact decomposition of the full origin-prefix defect。 -/
theorem criticalPrefixDefectZ_eq_actualOstrowskiPhaseDefectFold
    (n : ℕ)
    (y : ℤ) :
    criticalPrefixDefectZ n y =
      actualCriticalPhaseDefectFold
        0 (actualCriticalOstrowskiBlockScales n) y := by
  rw [criticalPrefixDefectZ_eq_interval_zero]
  have h :=
    criticalIntervalDefectZ_eq_phaseDefectFold
      0 (actualCriticalOstrowskiBlockScales n) y
  rw [actualCriticalOstrowskiBlockScales_mass_eq] at h
  simpa using h

end ExternalArithmetic
end CSTMicro
end Collatz2
