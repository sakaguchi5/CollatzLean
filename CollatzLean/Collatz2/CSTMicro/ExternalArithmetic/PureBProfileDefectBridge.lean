import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualOstrowskiBlockDecomposition
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ThreeQSmallStrip
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadPredecessorGeometry

/-!
# Pure B profile defect bridge

Stage 3/4 では critical prefix / shifted interval / Ostrowski phase block に対する
pure affine-defect calculus を構成した。このファイルでは minimal bad word `B` を
その calculus へ渡す最後の actual-to-pure bridge を作る。

`B` の final extra-depth profile を `h`、odd total を `m` とすると checkpoint

  p_k = beattyIndex k - h(k)

は actual odd-only prefix two-depth に一致する。従って

  A(h) = Σ_{k<m} 2^(p_k) 3^(m-1-k)

は `B` の affine constant そのものである。
一方 profile dyadic numerator `N(h)` は critical numerator から落とした量なので

  A(h) + N(h) = Ψ(m)

が exact に成立する。

さらに first-failure upper の normalized affine equation

  affineConst(B) = G * R_B + 2^H * q_B

と `2^H = 3^m + G` を結合し

  affineConst(B) - G * (R_B + q_B) = 3^m * q_B

を得る。したがって `y_B := R_B + q_B` と置けば

  Ψ(m) - N(h) - G*y_B = 3^m*q_B.

この時点で chain history / carry history は pure packet から消える。
minimality が与える全 predecessor inequality `q_B < D` だけは、後段で
boundary fragment を処理するため companion packet に保持する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-! ## 1. odd-only affine numerator as checkpoint sum -/

/-- odd-only word の cut `k` が affine numerator に与える unscaled term。 -/
def wordAffinePrefixTerm
    (w : Collatz2.Word)
    (k : ℕ) : ℕ :=
  2 ^ Collatz2.Word.prefixTwoDepth w k *
    3 ^ (Collatz2.Word.oddSteps w - (k + 1))

/-- odd-only affine numerator の prefix-depth finite sum。 -/
def wordAffinePrefixNumerator
    (w : Collatz2.Word) : ℕ :=
  Finset.sum (Finset.range (Collatz2.Word.oddSteps w))
    (fun k => wordAffinePrefixTerm w k)

/-- normalized cut term は affine-prefix term の exact 3 倍。 -/
theorem normalizedCutTerm_eq_three_mul_wordAffinePrefixTerm
    (w : Collatz2.Word)
    {k : ℕ}
    (hk : k < Collatz2.Word.oddSteps w) :
    Collatz2.Word.normalizedCutTerm w k =
      3 * wordAffinePrefixTerm w k := by
  have hExp :
      Collatz2.Word.oddSteps w - k =
        (Collatz2.Word.oddSteps w - (k + 1)) + 1 := by
    omega
  unfold Collatz2.Word.normalizedCutTerm wordAffinePrefixTerm
  rw [hExp, pow_succ]
  ring

/--
odd-only affine constant は checkpoint monomial の finite sumそのもの。

  affineConst(w) = Σ 2^prefixTwoDepth(k) 3^(m-1-k).
-/
theorem wordAffinePrefixNumerator_eq_affineConst
    (w : Collatz2.Word) :
    wordAffinePrefixNumerator w = Collatz2.Word.affineConst w := by
  have hSum := Collatz2.Word.sum_normalizedCutTerm_eq_three_mul_affineConst w
  have hScaled :
      3 * wordAffinePrefixNumerator w =
        3 * Collatz2.Word.affineConst w := by
    calc
      3 * wordAffinePrefixNumerator w
          =
        Finset.sum (Finset.range (Collatz2.Word.oddSteps w))
          (fun k => 3 * wordAffinePrefixTerm w k) := by
            unfold wordAffinePrefixNumerator
            rw [Finset.mul_sum]
      _ =
        Finset.sum (Finset.range (Collatz2.Word.oddSteps w))
          (fun k => Collatz2.Word.normalizedCutTerm w k) := by
            apply Finset.sum_congr rfl
            intro k hk
            symm
            exact
              normalizedCutTerm_eq_three_mul_wordAffinePrefixTerm
                w (Finset.mem_range.mp hk)
      _ = 3 * Collatz2.Word.affineConst w := hSum
  omega

/-! ## 2. first-passage profile is admissible and checkpoints are actual depths -/

/-- valid exponent word では consecutive prefix two-depth は strict に増える。 -/
theorem prefixTwoDepth_strict_succ_of_valid
    {w : Collatz2.Word}
    (hValid : Collatz2.Word.Valid w)
    {k : ℕ}
    (hk : k + 1 < Collatz2.Word.oddSteps w) :
    Collatz2.Word.prefixTwoDepth w k <
      Collatz2.Word.prefixTwoDepth w (k + 1) := by
  induction w generalizing k with
  | nil =>
      simp [Collatz2.Word.oddSteps] at hk
  | cons e t ih =>
      have he : 0 < e := hValid e (by simp)
      have hTailValid : Collatz2.Word.Valid t := by
        intro a ha
        exact hValid a (by simp [ha])
      cases k with
      | zero =>
          simp [
            Collatz2.Word.prefixTwoDepth,
            Collatz2.Word.twoSteps,
            he
          ]
      | succ k =>
          have hkTail :
              k + 1 < Collatz2.Word.oddSteps t := by
            simpa [Collatz2.Word.oddSteps] using hk
          have hIH := ih hTailValid hkTail
          have hAdd := Nat.add_lt_add_left hIH e
          simpa [
            Collatz2.Word.prefixTwoDepth,
            Collatz2.Word.twoSteps
          ] using hAdd

/-- first-passage parity word の odd-only prefix は critical roof 以下。 -/
theorem firstPassage_prefixTwoDepth_le_criticalHeight
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k : ℕ}
    (hk : k < Collatz2.Word.oddSteps (exponentWordOfParity v)) :
    Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) k ≤
      Collatz2.Word.criticalHeight k := by
  let w := exponentWordOfParity v
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using hFP.exponentWordOfParity_firstCrossing hLen
  by_cases hk0 : k = 0
  · subst k
    simp [Collatz2.Word.prefixTwoDepth, Collatz2.Word.criticalHeight]
  · exact
      hF.prefixTwoDepth_le_criticalHeight
        (Nat.pos_of_ne_zero hk0)
        (by simpa [w] using hk)

/--
first-passage endpoint の total two-depth は terminal odd count の Beatty positionの直後。

  H = beattyIndex(m) + 1.

proper endpoint `H-1` ではまだ `2^(H-1) < 3^m`、terminal では
`3^m < 2^H` なので、`beattyIndex m` は exact に `H-1` である。
-/
theorem firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    Collatz2.Word.twoSteps (exponentWordOfParity v) =
      beattyIndex (Collatz2.Word.oddSteps (exponentWordOfParity v)) + 1 := by
  let w := exponentWordOfParity v
  change
    Collatz2.Word.twoSteps w =
      beattyIndex (Collatz2.Word.oddSteps w) + 1
  have hTwo : Collatz2.Word.twoSteps w = v.length := by
    simpa [w] using hFP.twoSteps_exponentWordOfParity_eq_length hLen
  have hOdd : Collatz2.Word.oddSteps w = oddCount v := by
    simpa [w] using oddSteps_exponentWordOfParity v
  have hPredPos : 0 < v.length - 1 := by
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hPredPos.ne'
  have hEndpoint := endpointOddCount_eq_criticalPrefixHeight_pred hFP
  have hEndpoint' : oddCount v = criticalHeight (t + 1) := by
    rw [ht] at hEndpoint
    exact hEndpoint
  have hLow0 := criticalHeight_expanding (t + 1)
  have hLow : 2 ^ (v.length - 1) < 3 ^ oddCount v := by
    rw [ht, hEndpoint']
    exact hLow0
  have hContract := hFP.2.2
  unfold CoefficientContracting at hContract
  have hUpperCandidate :
      3 ^ oddCount v ≤ 2 ^ ((v.length - 1) + 1) := by
    have hLenEq : (v.length - 1) + 1 = v.length := by
      omega
    rw [hLenEq]
    exact Nat.le_of_lt hContract
  have hBetaLe : beattyIndex (oddCount v) ≤ v.length - 1 := by
    exact beattyIndex_le_of_upper hUpperCandidate
  have hPredLeBeta : v.length - 1 ≤ beattyIndex (oddCount v) := by
    by_contra hnot
    have hBetaLt : beattyIndex (oddCount v) < v.length - 1 := by
      omega
    have hUpper := beattyIndex_upper (oddCount v)
    have hExpLe : beattyIndex (oddCount v) + 1 ≤ v.length - 1 := by
      omega
    have hPowLe :
        2 ^ (beattyIndex (oddCount v) + 1) ≤
          2 ^ (v.length - 1) :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExpLe
    omega
  have hBeta : beattyIndex (oddCount v) = v.length - 1 := by
    omega
  rw [hTwo, hOdd, hBeta]
  omega

/-- actual extra-depth profile の checkpoint は actual prefix two-depth。 -/
theorem firstPassage_profileCheckpoint_eq_prefixTwoDepth
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k : ℕ}
    (hk : k < Collatz2.Word.oddSteps (exponentWordOfParity v)) :
    profileCheckpoint (parityExtraDepth v) k =
      Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) k := by
  apply profileCheckpoint_parityExtraDepth_eq_prefixTwoDepth
  exact firstPassage_prefixTwoDepth_le_criticalHeight hFP hLen hk

/--
first-passage endpoint の final extra-depth profile は pure admissible Sturmian profile。
-/
theorem firstPassage_admissibleSturmianProfile
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    AdmissibleSturmianProfile
      (Collatz2.Word.oddSteps (exponentWordOfParity v))
      (parityExtraDepth v) := by
  let w := exponentWordOfParity v
  have hValid : Collatz2.Word.Valid w := by
    simpa [w] using exponentWordOfParity_valid v
  apply admissibleSturmianProfile_of_parityExtraDepth
  · intro k hk
    exact firstPassage_prefixTwoDepth_le_criticalHeight hFP hLen hk
  · intro k hk
    have hStrict :=
      prefixTwoDepth_strict_succ_of_valid
        hValid
        (by simpa [w] using hk)
    simpa [w] using hStrict

/-! ## 3. pure profile affine numerator and critical correction -/

/-- admissible profile の checkpoint から作る affine numerator。 -/
def profileAffineNumerator
    (m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  Finset.sum (Finset.range m)
    (fun k =>
      2 ^ profileCheckpoint h k *
        3 ^ (m - (k + 1)))

/-- critical prefix の Nat-valued numerator。 -/
def criticalPrefixPhiNat
    (m : ℕ) : ℕ :=
  Finset.sum (Finset.range m)
    (fun k =>
      2 ^ beattyIndex k *
        3 ^ (m - (k + 1)))

/-- Nat critical prefix numerator は Stage 2 の integer `Ψ` に cast すると一致。 -/
theorem criticalPrefixPhiNat_cast_eq_criticalPrefixPhiZ
    (m : ℕ) :
    (criticalPrefixPhiNat m : ℤ) = criticalPrefixPhiZ m := by
  classical
  unfold criticalPrefixPhiNat criticalPrefixPhiZ
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < m := Finset.mem_range.mp hk
  have hExp : m - (k + 1) = m - 1 - k := by
    omega
  rw [hExp]

/--
critical numerator は actual checkpoint numerator と removed dyadic profile mass の和。

  A(h) + N(h) = Ψ(m).
-/
theorem profileAffineNumerator_add_profileDyadicCellNumerator_eq_criticalPrefixPhiNat
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h) :
    profileAffineNumerator m h +
        profileDyadicCellNumerator m h =
      criticalPrefixPhiNat m := by
  rw [profileDyadicCellNumerator_eq_closed A]
  unfold profileAffineNumerator
    profileDyadicClosedNumerator
    criticalPrefixPhiNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < m := Finset.mem_range.mp hk
  have hDepth : h k ≤ beattyIndex k := A.depth_le hkLt
  have hCheckpoint :
      profileCheckpoint h k = beattyIndex k - h k := rfl
  have hExpLe :
      beattyIndex k - h k ≤ beattyIndex k := by
    omega
  have hPowLe :
      2 ^ (beattyIndex k - h k) ≤ 2 ^ beattyIndex k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExpLe
  rw [hCheckpoint]
  unfold profileDyadicClosedColumn
  rw [← Nat.add_mul]
  rw [Nat.add_sub_of_le hPowLe]

/-- integer form: `A(h) = Ψ(m) - N(h)`。 -/
theorem profileAffineNumerator_cast_eq_criticalPrefixPhiZ_sub_profileDyadic
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h) :
    (profileAffineNumerator m h : ℤ) =
      criticalPrefixPhiZ m -
        (profileDyadicCellNumerator m h : ℤ) := by
  have hNat :=
    profileAffineNumerator_add_profileDyadicCellNumerator_eq_criticalPrefixPhiNat A
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hZ
  rw [criticalPrefixPhiNat_cast_eq_criticalPrefixPhiZ] at hZ
  linarith

/-- checkpoint が actual word prefix depth と一致すれば profile numerator は affineConst。 -/
theorem profileAffineNumerator_eq_affineConst_of_checkpoint
    {m : ℕ}
    {h : ℕ → ℕ}
    {w : Collatz2.Word}
    (hm : m = Collatz2.Word.oddSteps w)
    (hCheckpoint :
      ∀ k : ℕ, k < m →
        profileCheckpoint h k = Collatz2.Word.prefixTwoDepth w k) :
    profileAffineNumerator m h = Collatz2.Word.affineConst w := by
  have hSum :
      profileAffineNumerator m h = wordAffinePrefixNumerator w := by
    unfold profileAffineNumerator wordAffinePrefixNumerator
    rw [← hm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hCheckpoint k (Finset.mem_range.mp hk)]
    unfold wordAffinePrefixTerm
    rw [← hm]
  rw [hSum, wordAffinePrefixNumerator_eq_affineConst]

/-- first-passage endpoint では profile affine numerator が odd-only affine constant。 -/
theorem firstPassage_profileAffineNumerator_eq_wordAffineConst
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    profileAffineNumerator
        (Collatz2.Word.oddSteps (exponentWordOfParity v))
        (parityExtraDepth v) =
      Collatz2.Word.affineConst (exponentWordOfParity v) := by
  let w := exponentWordOfParity v
  apply
    profileAffineNumerator_eq_affineConst_of_checkpoint
      (m := Collatz2.Word.oddSteps w)
      (h := parityExtraDepth v)
      (w := w)
      rfl
  intro k hk
  simpa [w] using
    firstPassage_profileCheckpoint_eq_prefixTwoDepth
      hFP hLen (by simpa [w] using hk)

/-! ## 4. first-failure normalized equation at depth `m` -/

/--
first-failure upper exponent word の natural normalized dataを `3^m`-deep defectとして読む。

canonical witness は existence から選ばず、最初から

  y = upperR + q

と明示する。
-/
theorem FirstFailureEdge.deep_threeAdic_wordAffine_defect_explicit
    (F : FirstFailureEdge) :
    (Collatz2.Word.affineConst F.upperExponentWord : ℤ) -
        (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) *
          ((F.step.edge.upperR : ℤ) +
            (F.upperNormalizedDefectNat : ℤ)) =
      (3 : ℤ) ^ Collatz2.Word.oddSteps F.upperExponentWord *
        (F.upperNormalizedDefectNat : ℤ) := by
  let w := F.upperExponentWord
  let q := F.upperNormalizedDefectNat
  change
    (Collatz2.Word.affineConst w : ℤ) -
        (Collatz2.Word.terminalGap w : ℤ) *
          ((F.step.edge.upperR : ℤ) + (q : ℤ)) =
      (3 : ℤ) ^ Collatz2.Word.oddSteps w * (q : ℤ)
  have hAffineNat :=
    F.upperExponentWord_affineConst_eq_gap_mul_R_add_twoPow_mul_upperQ
  have hAffine :
      (Collatz2.Word.affineConst w : ℤ) =
        (Collatz2.Word.terminalGap w : ℤ) *
            (F.step.edge.upperR : ℤ) +
          (2 : ℤ) ^ Collatz2.Word.twoSteps w * (q : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hAffineNat
    push_cast at h
    simpa [w, q] using h
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using F.upperExponentWord_firstCrossing
  have hPow :
      3 ^ Collatz2.Word.oddSteps w <
        2 ^ Collatz2.Word.twoSteps w :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
      hF.terminalContracting
  have hGapNat :
      Collatz2.Word.terminalGap w +
          3 ^ Collatz2.Word.oddSteps w =
        2 ^ Collatz2.Word.twoSteps w := by
    unfold Collatz2.Word.terminalGap
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  have hGap := congrArg (fun n : ℕ => (n : ℤ)) hGapNat
  push_cast at hGap
  rw [hAffine]
  have hTwo :
      (2 : ℤ) ^ Collatz2.Word.twoSteps w =
        (Collatz2.Word.terminalGap w : ℤ) +
          (3 : ℤ) ^ Collatz2.Word.oddSteps w := by
    linarith
  rw [hTwo]
  ring

/--
同じ deep equation を満たす integer witness は一意。
terminal gap が strict positive なので cancellation できる。
-/
theorem FirstFailureEdge.deep_threeAdic_wordAffine_witness_unique
    (F : FirstFailureEdge)
    {y₁ y₂ : ℤ}
    (h₁ :
      (Collatz2.Word.affineConst F.upperExponentWord : ℤ) -
          (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) * y₁ =
        (3 : ℤ) ^ Collatz2.Word.oddSteps F.upperExponentWord *
          (F.upperNormalizedDefectNat : ℤ))
    (h₂ :
      (Collatz2.Word.affineConst F.upperExponentWord : ℤ) -
          (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) * y₂ =
        (3 : ℤ) ^ Collatz2.Word.oddSteps F.upperExponentWord *
          (F.upperNormalizedDefectNat : ℤ)) :
    y₁ = y₂ := by
  have hMul :
      (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) * y₁ =
        (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) * y₂ := by
    linarith
  have hF : Collatz2.Word.FirstCrossing F.upperExponentWord :=
    F.upperExponentWord_firstCrossing
  have hPow :
      3 ^ Collatz2.Word.oddSteps F.upperExponentWord <
        2 ^ Collatz2.Word.twoSteps F.upperExponentWord :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
      hF.terminalContracting
  have hGapPos : 0 < Collatz2.Word.terminalGap F.upperExponentWord := by
    unfold Collatz2.Word.terminalGap
    exact Nat.sub_pos_of_lt hPow
  have hGapNe :
      (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hGapPos)
  exact mul_left_cancel₀ hGapNe hMul

/-- existence 版は explicit canonical witness の薄い wrapper。 -/
theorem FirstFailureEdge.exists_deep_threeAdic_wordAffine_defect
    (F : FirstFailureEdge) :
    ∃ y : ℤ,
      (Collatz2.Word.affineConst F.upperExponentWord : ℤ) -
          (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) * y =
        (3 : ℤ) ^ Collatz2.Word.oddSteps F.upperExponentWord *
          (F.upperNormalizedDefectNat : ℤ) := by
  exact
    ⟨(F.step.edge.upperR : ℤ) +
        (F.upperNormalizedDefectNat : ℤ),
      deep_threeAdic_wordAffine_defect_explicit F⟩

/-! ## 5. pure obstruction packet -/

/--
Stage 6 以降が読む pure B profile obstruction。

ここには actual chain / carry ordering / representatives を残さない。
endpoint `(H,m)`, admissible profile `h`, tiny `q`, integer witness `y` と
one deep small-divisor equationだけを保持する。
-/
structure PureBProfileObstruction where
  H : ℕ
  m : ℕ
  h : ℕ → ℕ
  q : ℕ
  y : ℤ

  admissible : AdmissibleSturmianProfile m h

  gap_pos : 0 < columnLayerGap H m

  one_lt_m : 1 < m

  /-- terminal time is exactly one step after the `m`-th Beatty position. -/
  terminal_beatty : H = beattyIndex m + 1

  small_strip : 3 * q < m

  deep_profile_defect :
    criticalPrefixPhiZ m -
        (profileDyadicCellNumerator m h : ℤ) -
        (columnLayerGap H m : ℤ) * y =
      (3 : ℤ) ^ m * (q : ℤ)

namespace PureBProfileObstruction

/-- pure packet の terminal gap。 -/
def gap (P : PureBProfileObstruction) : ℕ :=
  columnLayerGap P.H P.m

/-- deep equation の左側を名前付き defect として読む。 -/
def profileDefect (P : PureBProfileObstruction) : ℤ :=
  criticalPrefixPhiZ P.m -
    (profileDyadicCellNumerator P.m P.h : ℤ) -
    (P.gap : ℤ) * P.y

/-- packet equation の wrapper。 -/
theorem profileDefect_eq_threePow_mul_q
    (P : PureBProfileObstruction) :
    P.profileDefect = (3 : ℤ) ^ P.m * (P.q : ℤ) := by
  exact P.deep_profile_defect

/-- pure defect は checkpoint affine numerator からも読める。 -/
theorem profileDefect_eq_profileAffine_sub_gap_mul_y
    (P : PureBProfileObstruction) :
    P.profileDefect =
      (profileAffineNumerator P.m P.h : ℤ) - (P.gap : ℤ) * P.y := by
  have hAffine :=
    profileAffineNumerator_cast_eq_criticalPrefixPhiZ_sub_profileDyadic
      P.admissible
  unfold profileDefect gap
  rw [← hAffine]

/-- pure defect は `3^m` で割れる。 -/
theorem threePow_dvd_profileDefect
    (P : PureBProfileObstruction) :
    (3 : ℤ) ^ P.m ∣ P.profileDefect := by
  rw [P.profileDefect_eq_threePow_mul_q]
  exact ⟨(P.q : ℤ), rfl⟩

end PureBProfileObstruction

/-! ## 6. minimal bad B -> pure packet, plus removable-corner companion -/

namespace MinimalActualABObstructionPacket

/-- pure B packet が使う actual first-failure edge。 -/
private def pureBFailureEdge
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    FirstFailureEdge :=
  M.actual.firstFailureEdge

/-- pure B packet が使う exponent word。 -/
private def pureBExponentWord
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    Collatz2.Word :=
  (pureBFailureEdge M).upperExponentWord

/-- pure B packet の terminal two-depth。 -/
private def pureBH
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : ℕ :=
  Collatz2.Word.twoSteps (pureBExponentWord M)

/-- pure B packet の odd depth。 -/
private def pureBm
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : ℕ :=
  Collatz2.Word.oddSteps (pureBExponentWord M)

/-- pure B packet の Sturmian profile。 -/
private def pureBh
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    ℕ → ℕ :=
  parityExtraDepth M.word

/--
actual first-failure edge の upper word は minimal bad word 自身。
wrapper をここで一度だけ剥がす。
-/
private theorem pureBFailureEdge_upperWord_eq_word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    (pureBFailureEdge M).step.edge.upperWord = M.word := by
  unfold pureBFailureEdge
  unfold ActualABObstructionPacket.firstFailureEdge
  unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
  unfold FirstFailureProvenance.toFirstFailureEdge
  dsimp
  exact M.failureStep_upperWord_eq_word

/-- pure exponent word は minimal bad word の parity encoding。 -/
private theorem pureBExponentWord_eq_exponentWordOfParity
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    pureBExponentWord M =
      exponentWordOfParity M.word := by
  unfold pureBExponentWord
  change
    exponentWordOfParity
        (pureBFailureEdge M).step.edge.upperWord =
      exponentWordOfParity M.word
  exact
    congrArg exponentWordOfParity
      (pureBFailureEdge_upperWord_eq_word M)

/--
deep equation の canonical witness。

existence theorem から witness を選び直さず、actual formula

  y = upperR + q

をそのまま定義にする。
-/
private def pureBDeepWitness
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    ℤ :=
  ((pureBFailureEdge M).step.edge.upperR : ℤ) +
    ((pureBFailureEdge M).upperNormalizedDefectNat : ℤ)

/-- explicit canonical witness の specification。 -/
private theorem pureBDeepWitness_spec
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    (Collatz2.Word.affineConst (pureBExponentWord M) : ℤ) -
        (Collatz2.Word.terminalGap (pureBExponentWord M) : ℤ) *
          pureBDeepWitness M =
      (3 : ℤ) ^ pureBm M *
        ((pureBFailureEdge M).upperNormalizedDefectNat : ℤ) := by
  simpa [
    pureBDeepWitness,
    pureBExponentWord,
    pureBm
  ] using
    FirstFailureEdge.deep_threeAdic_wordAffine_defect_explicit (pureBFailureEdge M)

/-- actual packet の q と first-failure normalized q は同じ。 -/
private theorem pureBFailureEdge_upperQ_eq_actualQ
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    (pureBFailureEdge M).upperNormalizedDefectNat =
      M.actual.q := by
  have hEq := M.actual.q_eq_canonical
  change
    M.actual.q =
      (pureBFailureEdge M).upperNormalizedDefectNat at hEq
  exact hEq.symm

/-- word terminal gap と pure column gap の同定。 -/
private theorem pureB_terminalGap_eq_columnLayerGap
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    Collatz2.Word.terminalGap (pureBExponentWord M) =
      columnLayerGap (pureBH M) (pureBm M) := by
  unfold pureBH pureBm
  unfold Collatz2.Word.terminalGap columnLayerGap
  rfl

/-- minimal bad word から得る profile は admissible。 -/
private theorem pureBProfile_admissible
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    AdmissibleSturmianProfile
      (pureBm M)
      (pureBh M) := by
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hFP : IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hA :=
    firstPassage_admissibleSturmianProfile hFP hLen
  rw [← pureBExponentWord_eq_exponentWordOfParity M] at hA
  simpa [
    pureBm,
    pureBh,
    pureBExponentWord
  ] using hA

/-- pure profile affine numerator は actual upper word の affine constant。 -/
private theorem pureBProfile_affine_eq_wordAffineConst
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    profileAffineNumerator
        (pureBm M)
        (pureBh M) =
      Collatz2.Word.affineConst
        (pureBExponentWord M) := by
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hFP : IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hA :=
    firstPassage_profileAffineNumerator_eq_wordAffineConst
      hFP hLen
  rw [← pureBExponentWord_eq_exponentWordOfParity M] at hA
  simpa [
    pureBm,
    pureBh,
    pureBExponentWord
  ] using hA

/-- pure packet の terminal gap は正。 -/
private theorem pureBProfile_gap_pos
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    0 < columnLayerGap (pureBH M) (pureBm M) := by
  have hFirstCrossing :
      Collatz2.Word.FirstCrossing
        (pureBExponentWord M) := by
    simpa [pureBExponentWord] using
      (pureBFailureEdge M).upperExponentWord_firstCrossing
  have hContract :
      3 ^ pureBm M < 2 ^ pureBH M := by
    simpa [pureBm, pureBH] using
      (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
        hFirstCrossing.terminalContracting
  unfold columnLayerGap
  exact Nat.sub_pos_of_lt hContract

/-- pure packet の odd depth は nontrivial。 -/
private theorem pureBProfile_one_lt_m
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    1 < pureBm M := by
  have hUpperLen :
      2 <
        (pureBFailureEdge M).step.edge.upperWord.length := by
    rw [pureBFailureEdge_upperWord_eq_word M]
    rw [M.word_length_eq]
    exact hL
  have hOdd :=
    (pureBFailureEdge M).one_lt_edge_oddTotal_of_two_lt_upperWord_length
      hUpperLen
  have hOddSteps :
      Collatz2.Word.oddSteps
          (pureBFailureEdge M).upperExponentWord =
        (pureBFailureEdge M).step.edge.oddTotal :=
    (pureBFailureEdge M).upperExponentWord_oddSteps
  unfold pureBm pureBExponentWord
  rw [hOddSteps]
  exact hOdd

/-- pure packet の terminal time は Beatty roof の一つ後。 -/
private theorem pureBProfile_terminal_beatty
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    pureBH M = beattyIndex (pureBm M) + 1 := by
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hFP : IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hT :=
    firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one
      hFP hLen
  rw [← pureBExponentWord_eq_exponentWordOfParity M] at hT
  simpa [
    pureBH,
    pureBm,
    pureBExponentWord
  ] using hT

/-- pure packet の q は tiny strip `3q < m` に入る。 -/
private theorem pureBProfile_small_strip
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    3 * M.actual.q < pureBm M := by
  have hSmall :=
    M.three_mul_actualQ_lt_oddCount hL
  have hOddCount :
      oddCount M.word = pureBm M := by
    calc
      oddCount M.word
          =
        oddCount
          (pureBFailureEdge M).step.edge.upperWord := by
            rw [pureBFailureEdge_upperWord_eq_word M]
      _ =
        (pureBFailureEdge M).step.edge.oddTotal :=
          (pureBFailureEdge M).step.edge.upperWord_oddCount
      _ =
        Collatz2.Word.oddSteps
          (pureBFailureEdge M).upperExponentWord := by
            exact
              (pureBFailureEdge M).upperExponentWord_oddSteps.symm
      _ = pureBm M := by
            rfl
  rw [hOddCount] at hSmall
  exact hSmall

/--
profile affine identity と actual deep equation を合成した
pure profile defect equation。
-/
private theorem pureBProfile_deep_defect
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    criticalPrefixPhiZ (pureBm M) -
        (profileDyadicCellNumerator
          (pureBm M)
          (pureBh M) : ℤ) -
        (columnLayerGap
          (pureBH M)
          (pureBm M) : ℤ) *
            pureBDeepWitness M =
      (3 : ℤ) ^ pureBm M *
        (M.actual.q : ℤ) := by
  have hAdmissible :=
    pureBProfile_admissible M hL
  have hProfileAffine :=
    pureBProfile_affine_eq_wordAffineConst M hL
  have hProfileCritical :=
    profileAffineNumerator_cast_eq_criticalPrefixPhiZ_sub_profileDyadic
      hAdmissible
  have hDeep :=
    pureBDeepWitness_spec M
  rw [pureB_terminalGap_eq_columnLayerGap M] at hDeep
  rw [pureBFailureEdge_upperQ_eq_actualQ M] at hDeep
  have hAffineZ :
      (profileAffineNumerator
        (pureBm M)
        (pureBh M) : ℤ) =
      (Collatz2.Word.affineConst
        (pureBExponentWord M) : ℤ) := by
    exact_mod_cast hProfileAffine
  rw [hProfileCritical] at hAffineZ
  rw [← hAffineZ] at hDeep
  exact hDeep

/-- minimal B から抽出する pure profile packet。 -/
def toPureBProfileObstruction
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    PureBProfileObstruction := {
  H := pureBH M
  m := pureBm M
  h := pureBh M
  q := M.actual.q
  y := pureBDeepWitness M
  admissible := pureBProfile_admissible M hL
  gap_pos := pureBProfile_gap_pos M
  one_lt_m := pureBProfile_one_lt_m M hL
  terminal_beatty := pureBProfile_terminal_beatty M hL
  small_strip := pureBProfile_small_strip M hL
  deep_profile_defect := pureBProfile_deep_defect M hL
}

/-- pure packet の `q` は元の minimal actual packet の `q` と同じ。 -/
theorem toPureBProfileObstruction_q_eq
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).q = M.actual.q := by
  rfl

/-- pure packet の witness は actual representative と q の和そのもの。 -/
theorem toPureBProfileObstruction_y_eq_upperR_add_q
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).y =
      ((M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
        (M.actual.q : ℤ)) := by
  change
    pureBDeepWitness M =
      ((M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
        (M.actual.q : ℤ))
  unfold pureBDeepWitness
  rw [pureBFailureEdge_upperQ_eq_actualQ M]
  rfl

/-- actual B 由来の pure witness は非負。 -/
theorem toPureBProfileObstruction_y_nonneg
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    0 ≤ (M.toPureBProfileObstruction hL).y := by
  rw [M.toPureBProfileObstruction_y_eq_upperR_add_q hL]
  positivity

/-- tiny quotient q は canonical witness y 以下。 -/
theorem toPureBProfileObstruction_q_le_y
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ((M.toPureBProfileObstruction hL).q : ℤ) ≤
      (M.toPureBProfileObstruction hL).y := by
  rw [M.toPureBProfileObstruction_q_eq hL]
  rw [M.toPureBProfileObstruction_y_eq_upperR_add_q hL]
  have hR :
      (0 : ℤ) ≤ (M.actual.firstFailureEdge.step.edge.upperR : ℤ) := by
    positivity
  linarith

/--
Stage 6 の boundary-fragment branch 用 companion property。
minimal B に入る任意の first-passage predecessor cell で pure packet の `q < D`。
-/
theorem pureProfileQ_lt_predecessor_residue
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    ((M.toPureBProfileObstruction hL).q : ℤ) <
      S.edge.toFareyCellPacket.residue := by
  rw [M.toPureBProfileObstruction_q_eq hL]
  exact M.predecessor_actualQ_lt_residue S hLowerFP

/-- 同じ predecessor cell は positive residue を持つ。 -/
theorem pureProfile_predecessor_residue_pos
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    0 < S.edge.toFareyCellPacket.residue := by
  exact M.predecessor_residue_pos S hLowerFP

/-- 同じ predecessor cell は terminal gap の内側にある。 -/
theorem pureProfile_predecessor_residue_lt_gap
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    S.edge.toFareyCellPacket.residue < S.edge.toFareyCellPacket.G := by
  exact M.predecessor_residue_lt_gap S hLowerFP

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
