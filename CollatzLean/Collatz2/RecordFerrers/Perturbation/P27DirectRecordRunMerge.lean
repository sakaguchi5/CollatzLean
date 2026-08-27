import CollatzLean.Collatz2.RecordFerrers.Perturbation.P26CanonicalAdjacentPairFlexibility

/-!
# Record–Ferrers 摂動理論 27: 連続 Record 区間の直接併合

P23–P26 では carry defect を実際の Ferrers 変形へ持ち上げた。
本ファイルでは、それとは独立な、より直接的な併合操作を構成する。

Record 区間の左端を `a`、右端を `c` とする。左端が critical roof 上にあるとき、
区間内部の excess をすべて `criticalExcess a` へ平坦化する。

  j ≤ a      : 元の excess
  a < j < c  : criticalExcess a
  c ≤ j      : 元の excess

この平坦化は Ferrers 単調性を保ち、critical roof の下側に留まるため、
同じ fixed chord の FirstCrossing target を与える。

さらに、連続する genuine RecordBlocks 全体をこの方法で平坦化すると、
その区間全体が一つの genuine RecordBlock になる。

* 右端が interior の場合は、各 Record edge の carry 1 を合成して outer carry 1 を得る。
* 右端が terminal の場合は、primitive + StripReduced の complement identity を使う。

最後に、変形区間の完全な左側・右側にある RecordBlock がそのまま保存されることも示す。
これにより次段で全体の RecordDecomposition を貼り直すための局所 API を用意する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 区間 `(a,c)` の内部だけを左端 roof の excess まで平坦化する。 -/
def flatIntervalExcess
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c j : ℕ) : ℕ :=
  if j ≤ a then
    u.excessAt j
  else if j < c then
    criticalExcess a
  else
    u.excessAt j

@[simp] theorem flatIntervalExcess_of_le_left
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c j : ℕ)
    (hj : j ≤ a) :
    flatIntervalExcess u a c j = u.excessAt j := by
  simp [flatIntervalExcess, hj]

@[simp] theorem flatIntervalExcess_of_inside
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c j : ℕ)
    (haj : a < j)
    (hjc : j < c) :
    flatIntervalExcess u a c j = criticalExcess a := by
  simp [flatIntervalExcess, not_le.mpr haj, hjc]

@[simp] theorem flatIntervalExcess_of_right
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c j : ℕ)
    (haj : a < j)
    (hcj : c ≤ j) :
    flatIntervalExcess u a c j = u.excessAt j := by
  simp [flatIntervalExcess, not_le.mpr haj, not_lt.mpr hcj]

/--
平坦化区間の右端は、terminal そのものか、source の roof contact とする。
-/
def FlatRightEndpoint
    {p H : ℕ}
    (u : FiberPoint p H)
    (c : ℕ) : Prop :=
  c = p ∨ RoofContact u c

/-- 平坦化 excess は非減少。 -/
theorem flatIntervalExcess_mono
    {p H : ℕ}
    (u : FiberPoint p H)
    {a c i j : ℕ}
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    (hij : i ≤ j)
    (hjp : j < p) :
    flatIntervalExcess u a c i ≤ flatIntervalExcess u a c j := by
  have hap : a < p := lt_of_lt_of_le hac hcp
  have hRoofAEx : u.excessAt a = criticalExcess a :=
    excessAt_eq_criticalExcess_of_roof hRoofA
  by_cases hjA : j ≤ a
  · have hiA : i ≤ a := le_trans hij hjA
    rw [flatIntervalExcess_of_le_left u a c i hiA,
        flatIntervalExcess_of_le_left u a c j hjA]
    exact u.excess_mono hij (Nat.le_of_lt hjp)
  · have hAj : a < j := by omega
    by_cases hiA : i ≤ a
    · rw [flatIntervalExcess_of_le_left u a c i hiA]
      by_cases hjC : j < c
      · rw [flatIntervalExcess_of_inside u a c j hAj hjC]
        have hMono := u.excess_mono hiA (Nat.le_of_lt hap)
        rw [hRoofAEx] at hMono
        exact hMono
      · have hCj : c ≤ j := by omega
        rw [flatIntervalExcess_of_right u a c j hAj hCj]
        exact u.excess_mono hij (Nat.le_of_lt hjp)
    · have hAi : a < i := by omega
      by_cases hiC : i < c
      · rw [flatIntervalExcess_of_inside u a c i hAi hiC]
        by_cases hjC : j < c
        · rw [flatIntervalExcess_of_inside u a c j hAj hjC]
        · have hCj : c ≤ j := by omega
          rw [flatIntervalExcess_of_right u a c j hAj hCj]
          rcases hRight with hTerminal | hRoofC
          · subst c
            omega
          · have hRoofCEx : u.excessAt c = criticalExcess c :=
              excessAt_eq_criticalExcess_of_roof hRoofC
            have hAC : criticalExcess a ≤ criticalExcess c :=
              criticalExcess_mono (Nat.le_of_lt hac)
            have hCJ := u.excess_mono hCj (Nat.le_of_lt hjp)
            rw [hRoofCEx] at hCJ
            exact hAC.trans hCJ
      · have hCi : c ≤ i := by omega
        have hCj : c ≤ j := le_trans hCi hij
        rw [flatIntervalExcess_of_right u a c i hAi hCi,
            flatIntervalExcess_of_right u a c j hAj hCj]
        exact u.excess_mono hij (Nat.le_of_lt hjp)

/-- 平坦化した自然数 profile を Ferrers shape にする。 -/
def flatIntervalShape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) : FerrersShape p :=
  { column := fun i => flatIntervalExcess u a c i.1
    mono := by
      intro i j hij
      exact flatIntervalExcess_mono
        u hac hcp hRoofA hRight hij j.isLt }

/-- 平坦化 shape は source と同じ fixed rectangle に入る。 -/
def flatIntervalFiberShape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) : FiberShape p H := by
  have hp : 0 < p := by omega
  have hpH : p ≤ H := by
    have h := FiberPoint.oddSteps_le_twoSteps_of_valid u.valid
    rw [u.oddSteps_eq, u.twoSteps_eq] at h
    exact h
  have hRoofAEx : u.excessAt a = criticalExcess a :=
    excessAt_eq_criticalExcess_of_roof hRoofA
  refine {
    shape := flatIntervalShape u a c hac hcp hRoofA hRight
    p_pos := hp
    p_le_H := hpH
    first_zero := ?_
    bounded := ?_
  }
  · change flatIntervalExcess u a c 0 = 0
    rw [flatIntervalExcess_of_le_left u a c 0 (Nat.zero_le _)]
    exact u.excessAt_zero
  · intro i
    change flatIntervalExcess u a c i.1 ≤ H - p
    by_cases hiA : i.1 ≤ a
    · rw [flatIntervalExcess_of_le_left u a c i.1 hiA]
      exact u.excess_le_rectangleHeight (Nat.le_of_lt i.isLt)
    · have hAi : a < i.1 := by omega
      by_cases hiC : i.1 < c
      · rw [flatIntervalExcess_of_inside u a c i.1 hAi hiC]
        rw [← hRoofAEx]
        exact u.excess_le_rectangleHeight (Nat.le_of_lt (lt_of_lt_of_le hac hcp))
      · have hCi : c ≤ i.1 := by omega
        rw [flatIntervalExcess_of_right u a c i.1 hAi hCi]
        exact u.excess_le_rectangleHeight (Nat.le_of_lt i.isLt)

/-- 平坦化 shape を exact fixed-chord point へ復号する。 -/
def flatIntervalTarget
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) : FiberPoint p H :=
  (flatIntervalFiberShape u a c hac hcp hRoofA hRight).toFiberPoint

/-- 平坦化 target の proper height。 -/
theorem flatIntervalTarget_height
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    {j : ℕ}
    (hjp : j < p) :
    (flatIntervalTarget u a c hac hcp hRoofA hRight).height j =
      j + flatIntervalExcess u a c j := by
  let S := flatIntervalFiberShape u a c hac hcp hRoofA hRight
  let v := flatIntervalTarget u a c hac hcp hRoofA hRight
  have hShape := S.toFerrersShape_toFiberPoint
  have hCol := congrArg
    (fun T : FerrersShape p => T.column ⟨j, hjp⟩) hShape
  have hEx : v.excessAt j = flatIntervalExcess u a c j := by
    dsimp [v, S] at hCol ⊢
    change
      (flatIntervalFiberShape u a c hac hcp hRoofA hRight).toFiberPoint.excessAt j =
        flatIntervalExcess u a c j
    calc
      (flatIntervalFiberShape u a c hac hcp hRoofA hRight).toFiberPoint.excessAt j
          =
        (flatIntervalFiberShape u a c hac hcp hRoofA hRight).shape.column ⟨j, hjp⟩ :=
            hCol
      _ = flatIntervalExcess u a c j := by
            rfl
  have hHeight := v.height_eq_index_add_excess (Nat.le_of_lt hjp)
  rw [hEx] at hHeight
  exact hHeight

/-- 左端 roof は target でも保存される。 -/
theorem flatIntervalTarget_leftRoof
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) :
    RoofContact (flatIntervalTarget u a c hac hcp hRoofA hRight) a := by
  have hap : a < p := lt_of_lt_of_le hac hcp
  have hHeight := flatIntervalTarget_height
    u a c hac hcp hRoofA hRight hap
  have hEx := flatIntervalExcess_of_le_left u a c a le_rfl
  rw [hEx] at hHeight
  unfold RoofContact at hRoofA ⊢
  have hSource := u.height_eq_index_add_excess (Nat.le_of_lt hap)
  rw [hRoofA] at hSource
  omega

/-- proper な右端 roof も target で保存される。 -/
theorem flatIntervalTarget_rightRoof
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    (hcpLt : c < p) :
    RoofContact
      (flatIntervalTarget u a c hac hcp hRoofA (Or.inr hRoofC)) c := by
  have hHeight := flatIntervalTarget_height
    u a c hac hcp hRoofA (Or.inr hRoofC) hcpLt
  have hEx := flatIntervalExcess_of_right u a c c hac le_rfl
  rw [hEx] at hHeight
  unfold RoofContact at hRoofC ⊢
  have hSource := u.height_eq_index_add_excess (Nat.le_of_lt hcpLt)
  rw [hRoofC] at hSource
  omega

/-- 平坦化 target は区間外で source height と一致する。 -/
theorem flatIntervalTarget_height_eq_source_of_outside
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    {j : ℕ}
    (hjp : j ≤ p)
    (hOutside : j ≤ a ∨ c ≤ j) :
    (flatIntervalTarget u a c hac hcp hRoofA hRight).height j =
      u.height j := by
  by_cases hjLt : j < p
  · have hHeight := flatIntervalTarget_height
      u a c hac hcp hRoofA hRight hjLt
    have hEx : flatIntervalExcess u a c j = u.excessAt j := by
      rcases hOutside with hJA | hCJ
      · exact flatIntervalExcess_of_le_left u a c j hJA
      · have hAJ : a < j := by omega
        exact flatIntervalExcess_of_right u a c j hAJ hCJ
    rw [hEx] at hHeight
    have hSource := u.height_eq_index_add_excess (Nat.le_of_lt hjLt)
    exact hHeight.trans hSource.symm
  · have hjEq : j = p := by omega
    subst j
    simp

/-- 平坦化は actual compact-support replacement。 -/
theorem flatIntervalTarget_blockReplacement
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c) :
    BlockReplacement u
      (flatIntervalTarget u a c hac hcp hRoofA hRight) a c := by
  refine {
    start_lt_stop := hac
    stop_le_terminal := hcp
    outside := ?_
  }
  intro j hjp hOutside
  have hEq := flatIntervalTarget_height_eq_source_of_outside
    u a c hac hcp hRoofA hRight hjp hOutside
  unfold profileDisplacement
  rw [hEq]
  ring

/-- 平坦化 shape は critical roof の下側にある。 -/
theorem flatIntervalShape_isCriticalSubshape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    (hFu : FirstCrossing u.word) :
    IsCriticalSubshape (flatIntervalShape u a c hac hcp hRoofA hRight) := by
  have hp : 0 < p := by omega
  have hContract : ContractingChord p H := by
    have hPow := (contracting_iff_threePow_lt_twoPow).1 hFu.terminalContracting
    simpa [ContractingChord, u.oddSteps_eq, u.twoSteps_eq] using hPow
  have hSource : IsCriticalSubshape u.toFerrersShape :=
    (firstCrossing_iff_criticalSubshape u hp hContract).1 hFu
  intro i
  have hSourceI := hSource i
  change u.excessAt i.1 ≤ criticalExcess i.1 at hSourceI
  change flatIntervalExcess u a c i.1 ≤ criticalExcess i.1
  by_cases hiA : i.1 ≤ a
  · rw [flatIntervalExcess_of_le_left u a c i.1 hiA]
    exact hSourceI
  · have hAi : a < i.1 := by omega
    by_cases hiC : i.1 < c
    · rw [flatIntervalExcess_of_inside u a c i.1 hAi hiC]
      exact criticalExcess_mono (Nat.le_of_lt hAi)
    · have hCi : c ≤ i.1 := by omega
      rw [flatIntervalExcess_of_right u a c i.1 hAi hCi]
      exact hSourceI

/-- 平坦化 target は whole FirstCrossing を保つ。 -/
theorem flatIntervalTarget_firstCrossing
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    (hFu : FirstCrossing u.word) :
    FirstCrossing (flatIntervalTarget u a c hac hcp hRoofA hRight).word := by
  have hContract : ContractingChord p H := by
    have hPow := (contracting_iff_threePow_lt_twoPow).1 hFu.terminalContracting
    simpa [ContractingChord, u.oddSteps_eq, u.twoSteps_eq] using hPow
  unfold flatIntervalTarget
  apply
    ((flatIntervalFiberShape u a c hac hcp hRoofA hRight).firstCrossing_toFiberPoint_iff
      hContract).2
  exact flatIntervalShape_isCriticalSubshape
    u a c hac hcp hRoofA hRight hFu

/-- 区間内部では、左端からの actual two-depth は odd 長そのもの。 -/
theorem flatIntervalTarget_localDepth_eq_index
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    {j : ℕ}
    (hjPos : 0 < j)
    (hajc : a + j < c) :
    twoSteps
      (blockWord
        (flatIntervalTarget u a c hac hcp hRoofA hRight) a j) = j := by
  let v := flatIntervalTarget u a c hac hcp hRoofA hRight
  have hAjp : a + j < p := lt_of_lt_of_le hajc hcp
  have hA : RoofContact v a :=
    flatIntervalTarget_leftRoof u a c hac hcp hRoofA hRight
  have hJ := flatIntervalTarget_height
    u a c hac hcp hRoofA hRight hAjp
  have hEx : flatIntervalExcess u a c (a + j) = criticalExcess a := by
    apply flatIntervalExcess_of_inside
    · omega
    · exact hajc
  rw [hEx] at hJ
  have hAdd := height_add_eq_add_blockDepth v a j
  unfold RoofContact at hA
  rw [hA, hJ] at hAdd
  unfold criticalExcess at hAdd
  have hBase := index_le_criticalHeight a
  have hLeft :
      a + j + (criticalHeight a - a) =
        criticalHeight a + j := by
    calc
      a + j + (criticalHeight a - a)
          = (a + (criticalHeight a - a)) + j := by
              ac_rfl
      _ = criticalHeight a + j := by
            rw [Nat.add_sub_of_le hBase]
  have hEq :
      criticalHeight a + j =
        criticalHeight a + (blockWord v a j).twoSteps := by
    exact hLeft.symm.trans hAdd
  have hDepth :
      j = (blockWord v a j).twoSteps :=
    Nat.add_left_cancel hEq
  exact hDepth.symm

/-- primitive + StripReduced で minimal-depth の global rank drop に必要な不等式。 -/
theorem chordDrop_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {len : ℕ}
    (hLenPos : 0 < len)
    (hLenLt : len < P.oddCount) :
    P.twoDepth * len <
      P.oddCount * (criticalHeight len + 1) := by
  have hRange :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hLenPos hLenLt
  have hStripLt :
      P.twoDepth * len -
          P.oddCount * criticalHeight len <
        P.oddCount := by
    simpa [Word.ContractingExponentPair.stripRank] using hRange.2
  rw [Nat.mul_add, Nat.mul_one]
  have hLower := P.criticalHeight_below_chord hLenPos
  omega

/--
平坦化区間の total depth が minimal depth なら、その local word は MinimalBlock。
-/
theorem flatIntervalTarget_minimalBlock_of_totalDepth
    {p H : ℕ}
    (u : FiberPoint p H)
    (a c len : ℕ)
    (hac : a < c)
    (hcp : c ≤ p)
    (hRoofA : RoofContact u a)
    (hRight : FlatRightEndpoint u c)
    (hEnd : a + len = c)
    (hLenPos : 0 < len)
    (hTotal :
      twoSteps
        (blockWord
          (flatIntervalTarget u a c hac hcp hRoofA hRight) a len) =
        criticalHeight len + 1) :
    MinimalBlock
      (blockWord
        (flatIntervalTarget u a c hac hcp hRoofA hRight) a len) := by
  let v := flatIntervalTarget u a c hac hcp hRoofA hRight
  have hEndLe : a + len ≤ p := by rw [hEnd]; exact hcp
  have hOdd : oddSteps (blockWord v a len) = len :=
    oddSteps_blockWord v hEndLe
  have hFirst : FirstCrossing (blockWord v a len) := by
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      have hPosOdd : 0 < oddSteps (blockWord v a len) := by
        rw [hOdd]
        exact hLenPos
      simpa [oddSteps] using hPosOdd
    · intro j hjPos hjLtWord
      have hLenWord : (blockWord v a len).length = len := by
        simpa [oddSteps] using hOdd
      have hjLt : j < len := by
        simpa [hLenWord] using hjLtWord
      have hTake : (blockWord v a len).take j = blockWord v a j := by
        simp [blockWord, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
      have hDepth : twoSteps (blockWord v a j) = j := by
        apply flatIntervalTarget_localDepth_eq_index
          u a c hac hcp hRoofA hRight hjPos
        rw [← hEnd]
        omega
      have hOddJ : oddSteps (blockWord v a j) = j :=
        oddSteps_blockWord v (by omega)
      apply (expanding_iff_twoPow_lt_threePow).2
      rw [hTake, hDepth, hOddJ]
      have hCrit := criticalHeight_pow_lt_threePow hjPos
      have hIdx := index_le_criticalHeight j
      have hPowLe : 2 ^ j ≤ 2 ^ criticalHeight j :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hIdx
      exact lt_of_le_of_lt hPowLe hCrit
    · apply contracting_of_twoSteps_eq_minimalDepth
      · rw [hOdd]
        exact hLenPos
      · unfold minimalDepth
        rw [hOdd]
        exact hTotal
  exact {
    firstCrossing := hFirst
    minimalDepth := by
      rw [hOdd]
      exact hTotal
  }

/--
terminal より手前で終わる、連続した genuine RecordBlock 区間。
-/
inductive InteriorRecordRun
    {p H : ℕ}
    (u : FiberPoint p H) : ℕ → List ℕ → ℕ → Type
  | one
      {start len : ℕ}
      (block : RecordBlock u start len)
      (stopInterior : start + len < p) :
      InteriorRecordRun u start [len] (start + len)
  | cons
      {start len stop : ℕ}
      {rest : List ℕ}
      (block : RecordBlock u start len)
      (blockInterior : start + len < p)
      (tail : InteriorRecordRun u (start + len) rest stop) :
      InteriorRecordRun u start (len :: rest) stop

namespace InteriorRecordRun

/-- 連続区間の長さ和は右端までの距離。 -/
theorem start_add_sum_eq_stop
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    start + lengths.sum = stop := by
  induction R with
  | one B hInterior => simp
  | cons B hInterior T ih =>
      simp only [List.sum_cons]
      omega

/-- 連続区間の全長は正。 -/
theorem sum_pos
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    0 < lengths.sum := by
  cases R with
  | one B hInterior =>
      simpa using B.length_pos
  | cons B hInterior T =>
      simp only [List.sum_cons]
      exact lt_of_lt_of_le
        B.length_pos
        (Nat.le_add_right _ _)

/-- 右端は terminal より手前。 -/
theorem stop_lt_terminal
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    stop < p := by
  induction R with
  | one B hInterior => exact hInterior
  | cons B hInterior T ih => exact ih

/-- 左端は source roof 上。 -/
theorem startRoof
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    RoofContact u start := by
  cases R with
  | one B hInterior =>
      unfold RoofContact
      exact B.start_roof
  | cons B hInterior T =>
      unfold RoofContact
      exact B.start_roof

/-- 右端も source roof 上。 -/
theorem stopRoof
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    RoofContact u stop := by
  induction R with
  | one B hInterior =>
      unfold RoofContact
      simpa using B.next_roof_if_interior hInterior
  | cons B hInterior T ih => exact ih

/-- 連続 interior Record 区間の outer carry は 1。 -/
theorem outerCarry_one
    {p H : ℕ}
    {u : FiberPoint p H}
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    criticalCarry start lengths.sum = 1 := by
  induction R with
  | one B hInterior =>
      simpa using B.criticalCarry_eq_one_of_interior hInterior
  | @cons start len stop rest B hInterior T ih =>
      have hFirst : criticalCarry start len = 1 :=
        B.criticalCarry_eq_one_of_interior hInterior
      have hCoc := criticalCarry_cocycle start len rest.sum
      rw [hFirst, ih] at hCoc
      have hLocal := criticalCarry_le_one len rest.sum
      have hOuter := criticalCarry_le_one start (len + rest.sum)
      simp only [List.sum_cons]
      omega

end InteriorRecordRun

/--
## 主定理 1: interior の連続 Record 区間を一つへ直接併合
-/
theorem directInteriorRecordRunMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      BlockReplacement u v start stop ∧
      FirstCrossing v.word ∧
      RecordBlock v start lengths.sum := by
  let len := lengths.sum
  have hLenPos : 0 < len := by simpa [len] using R.sum_pos
  have hEnd : start + len = stop := by
    simpa [len] using R.start_add_sum_eq_stop
  have hStopLt : stop < P.oddCount := R.stop_lt_terminal
  have hStartStop : start < stop := by omega
  have hRoofA : RoofContact u start := R.startRoof
  have hRoofC : RoofContact u stop := R.stopRoof
  let v : FiberPoint P.oddCount P.twoDepth :=
    flatIntervalTarget u start stop hStartStop
      (Nat.le_of_lt hStopLt) hRoofA (Or.inr hRoofC)
  have hRep : BlockReplacement u v start stop := by
    dsimp [v]
    exact flatIntervalTarget_blockReplacement
      u start stop hStartStop (Nat.le_of_lt hStopLt) hRoofA (Or.inr hRoofC)
  have hFv : FirstCrossing v.word := by
    dsimp [v]
    exact flatIntervalTarget_firstCrossing
      u start stop hStartStop (Nat.le_of_lt hStopLt) hRoofA (Or.inr hRoofC) hFu
  have hRoofStart : RoofContact v start := by
    dsimp [v]
    exact flatIntervalTarget_leftRoof
      u start stop hStartStop (Nat.le_of_lt hStopLt) hRoofA (Or.inr hRoofC)
  have hRoofStop : RoofContact v stop := by
    dsimp [v]
    exact flatIntervalTarget_rightRoof
      u start stop hStartStop (Nat.le_of_lt hStopLt) hRoofA hRoofC hStopLt
  have hCarry : criticalCarry start len = 1 := by
    simpa [len] using R.outerCarry_one
  have hHeight := height_add_eq_add_blockDepth v start len
  have hCrit := criticalHeight_add_eq start len
  unfold RoofContact at hRoofStart hRoofStop
  rw [hEnd, hRoofStart, hRoofStop] at hHeight
  rw [hCarry] at hCrit
  have hTotal :
      twoSteps (blockWord v start len) = criticalHeight len + 1 := by
    have hCritStop :
        criticalHeight stop =
          criticalHeight start + (criticalHeight len + 1) := by
      rw [← hEnd]
      simpa [Nat.add_assoc] using hCrit
    have hEq :
        criticalHeight start +
            twoSteps (blockWord v start len) =
          criticalHeight start +
            (criticalHeight len + 1) := by
      exact hHeight.symm.trans hCritStop
    exact Nat.add_left_cancel hEq
  have hMinimal : MinimalBlock (blockWord v start len) := by
    dsimp [v]
    exact flatIntervalTarget_minimalBlock_of_totalDepth
      u start stop len hStartStop (Nat.le_of_lt hStopLt)
      hRoofA (Or.inr hRoofC) hEnd hLenPos hTotal
  have hLenLt : len < P.oddCount := by omega
  have hDrop := chordDrop_of_primitiveReduced
    P hPrimitive hReduced hLenPos hLenLt
  have hMerged : RecordBlock v start len := by
    apply RecordBlock.ofMinimalAtRoof
      v hLenPos (by omega) hMinimal hRoofStart
    · intro j hjPos _hjLt
      exact P.criticalHeight_below_chord hjPos
    · exact hDrop
    · intro _hInterior
      rw [hEnd]
      exact hRoofStop
  exact ⟨v, hRep, hFv, by simpa [len] using hMerged⟩

namespace RecordChain

/-- terminal までの RecordChain の全長は正。 -/
theorem sum_pos
    {p H : ℕ}
    {u : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths) :
    0 < lengths.sum := by
  cases C with
  | last B hTerminal =>
      simpa using B.length_pos
  | cons B hInterior T =>
      simp only [List.sum_cons]
      exact lt_of_lt_of_le
        B.length_pos
        (Nat.le_add_right _ _)

/-- terminal までの chain の左端は roof 上。 -/
theorem startRoof
    {p H : ℕ}
    {u : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths) :
    RoofContact u start := by
  cases C with
  | last B hTerminal =>
      unfold RoofContact
      exact B.start_roof
  | cons B hInterior T =>
      unfold RoofContact
      exact B.start_roof

end RecordChain

/--
## 主定理 2: terminal までの連続 Record 区間を一つへ直接併合

defect split は使わない。primitive + StripReduced の complement identity だけを使う。
-/
theorem directTerminalRecordRunMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hStartPos : 0 < start) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      BlockReplacement u v start P.oddCount ∧
      FirstCrossing v.word ∧
      RecordBlock v start lengths.sum := by
  let len := lengths.sum
  have hLenPos : 0 < len := by simpa [len] using C.sum_pos
  have hEnd : start + len = P.oddCount := by
    simpa [len] using C.start_add_sum_eq_terminal
  have hStartLt : start < P.oddCount := by omega
  have hRoofA : RoofContact u start := C.startRoof
  let v : FiberPoint P.oddCount P.twoDepth :=
    flatIntervalTarget u start P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl)
  have hRep : BlockReplacement u v start P.oddCount := by
    dsimp [v]
    exact flatIntervalTarget_blockReplacement
      u start P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl)
  have hFv : FirstCrossing v.word := by
    dsimp [v]
    exact flatIntervalTarget_firstCrossing
      u start P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl) hFu
  have hRoofStart : RoofContact v start := by
    dsimp [v]
    exact flatIntervalTarget_leftRoof
      u start P.oddCount hStartLt le_rfl hRoofA (Or.inl rfl)
  have hComplement :=
    criticalHeight_add_complement_add_one_eq_twoDepth_of_primitiveReduced
      P hPrimitive hReduced hStartPos hStartLt
  have hLenEq : len = P.oddCount - start := by omega
  rw [← hLenEq] at hComplement
  have hHeight := height_add_eq_add_blockDepth v start len
  unfold RoofContact at hRoofStart
  rw [hEnd, v.height_terminal, hRoofStart] at hHeight
  have hTotal :
      twoSteps (blockWord v start len) = criticalHeight len + 1 := by
    omega
  have hMinimal : MinimalBlock (blockWord v start len) := by
    dsimp [v]
    exact flatIntervalTarget_minimalBlock_of_totalDepth
      u start P.oddCount len hStartLt le_rfl hRoofA (Or.inl rfl)
      hEnd hLenPos hTotal
  have hLenLt : len < P.oddCount := by omega
  have hDrop := chordDrop_of_primitiveReduced
    P hPrimitive hReduced hLenPos hLenLt
  have hMerged : RecordBlock v start len := by
    apply RecordBlock.ofMinimalAtRoof
      v hLenPos (by omega) hMinimal hRoofStart
    · intro j hjPos _hjLt
      exact P.criticalHeight_below_chord hjPos
    · exact hDrop
    · intro hInterior
      rw [hEnd] at hInterior
      omega
  exact ⟨v, hRep, hFv, by simpa [len] using hMerged⟩

/--
## 主定理 3: genuine adjacent pair は interior / terminal を問わず直接 merge できる
-/
theorem directAdjacentRecordMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (hPair :
      AdjacentInteriorRecordPair P u a r s ∨
        AdjacentTerminalRecordPair P u a r s) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      BlockReplacement u v a ((a + r) + s) ∧
      FirstCrossing v.word ∧
      RecordBlock v a (r + s) := by
  rcases hPair with A | T
  · let R : InteriorRecordRun u a [r, s] ((a + r) + s) :=
      InteriorRecordRun.cons A.leftSource A.leftInterior
        (InteriorRecordRun.one A.rightSource A.outerInterior)
    obtain ⟨v, hRep, hFv, hMerged⟩ :=
      directInteriorRecordRunMerge P hPrimitive hReduced u hFu R
    have hSum : ([r, s] : List ℕ).sum = r + s := by simp
    rw [hSum] at hMerged
    exact ⟨v, hRep, hFv, hMerged⟩
  · let C : RecordChain u a [r, s] :=
      RecordChain.cons T.leftSource T.leftInterior
        (RecordChain.last T.rightSource T.outerTerminal)
    obtain ⟨v, hRep0, hFv, hMerged⟩ :=
      directTerminalRecordRunMerge
        P hPrimitive hReduced u hFu C T.anchor_pos
    have hStop : (a + r) + s = P.oddCount := T.outerTerminal
    have hRep : BlockReplacement u v a ((a + r) + s) := by
      simpa [hStop] using hRep0
    have hSum : ([r, s] : List ℕ).sum = r + s := by simp
    rw [hSum] at hMerged
    exact ⟨v, hRep, hFv, hMerged⟩

/-! ## 変形区間の外側にある RecordBlock の保存 -/

namespace BlockReplacement

/-- replacement 左側の任意 cut では height が不変。 -/
theorem height_eq_of_le_start
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {k : ℕ}
    (hk : k ≤ a) :
    u.height k = v.height k := by
  have hkp : k ≤ p :=
    le_trans hk (le_trans (Nat.le_of_lt R.start_lt_stop) R.stop_le_terminal)
  have hDisp := R.outside k hkp (Or.inl hk)
  unfold profileDisplacement at hDisp
  exact_mod_cast (sub_eq_zero.mp hDisp).symm

/-- replacement 右側の任意 cut でも height が不変。 -/
theorem height_eq_of_stop_le
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {k : ℕ}
    (hk : c ≤ k)
    (hkp : k ≤ p) :
    u.height k = v.height k := by
  have hDisp := R.outside k hkp (Or.inr hk)
  unfold profileDisplacement at hDisp
  exact_mod_cast (sub_eq_zero.mp hDisp).symm

end BlockReplacement

/-- 両端 height が同じなら、その区間の actual two-depth も同じ。 -/
theorem blockDepth_eq_of_endpointHeights
    {p H : ℕ}
    {u v : FiberPoint p H}
    {start len : ℕ}
    (hStart : u.height start = v.height start)
    (hEnd : u.height (start + len) = v.height (start + len)) :
    twoSteps (blockWord u start len) =
      twoSteps (blockWord v start len) := by
  have hU := height_add_eq_add_blockDepth u start len
  have hV := height_add_eq_add_blockDepth v start len
  omega

/--
source RecordBlock の全 cut で target と source の height / rank が一致するなら、
RecordBlock は target でも保存される。
-/
theorem recordBlock_preserved_of_equal_data
    {p H : ℕ}
    {u v : FiberPoint p H}
    {start len : ℕ}
    (B : RecordBlock u start len)
    (hHeight :
      ∀ j : ℕ, j ≤ len →
        u.height (start + j) = v.height (start + j))
    (hRank :
      ∀ j : ℕ, j ≤ len →
        chordRankInt v.word (start + j) =
          chordRankInt u.word (start + j)) :
    RecordBlock v start len := by
  have hEnd : start + len ≤ p := B.end_le_terminal
  have hOddV : oddSteps (blockWord v start len) = len :=
    oddSteps_blockWord v hEnd
  have hOddU : oddSteps (blockWord u start len) = len := B.local_oddSteps
  have hTotalEq :
      twoSteps (blockWord u start len) =
        twoSteps (blockWord v start len) := by
    apply blockDepth_eq_of_endpointHeights
    · simpa using hHeight 0 (Nat.zero_le _)
    · exact hHeight len le_rfl
  have hTotalV :
      twoSteps (blockWord v start len) = criticalHeight len + 1 := by
    rw [← hTotalEq]
    exact B.local_twoSteps
  have hFirstV : FirstCrossing (blockWord v start len) := by
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      have : 0 < oddSteps (blockWord v start len) := by
        rw [hOddV]
        exact B.length_pos
      simpa [oddSteps] using this
    · intro j hjPos hjLtWord
      have hLenWord : (blockWord v start len).length = len := by
        simpa [oddSteps] using hOddV
      have hjLt : j < len := by simpa [hLenWord] using hjLtWord
      have hUStart := hHeight 0 (Nat.zero_le _)
      have hUJ := hHeight j (Nat.le_of_lt hjLt)
      have hDepthEq :
          twoSteps (blockWord u start j) =
            twoSteps (blockWord v start j) := by
        apply blockDepth_eq_of_endpointHeights
        · simpa using hUStart
        · simpa using hUJ
      have hTakeU : (blockWord u start len).take j = blockWord u start j := by
        simp [blockWord, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
      have hTakeV : (blockWord v start len).take j = blockWord v start j := by
        simp [blockWord, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
      have hExpU := B.minimal.firstCrossing.properExpanding hjPos (by
        have hLenU : (blockWord u start len).length = len := by
          simpa [oddSteps] using hOddU
        simpa [hLenU] using hjLt)
      have hPowU := (expanding_iff_twoPow_lt_threePow).1 hExpU
      have hOddUJ : oddSteps (blockWord u start j) = j :=
        oddSteps_blockWord u (by omega)
      have hOddVJ : oddSteps (blockWord v start j) = j :=
        oddSteps_blockWord v (by omega)
      apply (expanding_iff_twoPow_lt_threePow).2
      rw [hTakeV]
      rw [hTakeU] at hPowU
      simpa [hDepthEq, hOddUJ, hOddVJ] using hPowU
    · apply contracting_of_twoSteps_eq_minimalDepth
      · rw [hOddV]
        exact B.length_pos
      · unfold minimalDepth
        rw [hOddV]
        exact hTotalV
  refine {
    length_pos := B.length_pos
    end_le_terminal := B.end_le_terminal
    minimal := ⟨hFirstV, ?_⟩
    start_roof := ?_
    interior_above := ?_
    terminal_below := ?_
    next_roof_if_interior := ?_
  }
  · rw [hOddV]
    exact hTotalV
  · have h := hHeight 0 (Nat.zero_le _)
    simpa [B.start_roof] using h.symm
  · intro j hjPos hjLt
    have hS : chordRankInt v.word start = chordRankInt u.word start := by
      simpa using hRank 0 (Nat.zero_le _)
    have hJ := hRank j (Nat.le_of_lt hjLt)
    have hOld := B.interior_above j hjPos hjLt
    rw [hS, hJ]
    exact hOld
  · have hS : chordRankInt v.word start = chordRankInt u.word start := by
      simpa using hRank 0 (Nat.zero_le _)
    have hE := hRank len le_rfl
    rw [hS, hE]
    exact B.terminal_below
  · intro hInterior
    have h := hHeight len le_rfl
    have hOld := B.next_roof_if_interior hInterior
    rw [hOld] at h
    exact h.symm

namespace RecordBlock

/-- replacement 区間より完全に左の RecordBlock は保存される。 -/
theorem preserved_on_left
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len : ℕ}
    (B : RecordBlock u start len)
    (hLeft : start + len ≤ a) :
    RecordBlock v start len := by
  apply recordBlock_preserved_of_equal_data B
  · intro j hjLe
    have hk : start + j ≤ a := by omega
    have hEq := R.height_eq_of_le_start hk
    exact hEq
  · intro j hjLe
    have hk : start + j ≤ a := by omega
    exact R.chordRankInt_outside
      (le_trans hk (le_trans (Nat.le_of_lt R.start_lt_stop) R.stop_le_terminal))
      (Or.inl hk)

/-- replacement 区間より完全に右の RecordBlock も保存される。 -/
theorem preserved_on_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v a c)
    {start len : ℕ}
    (B : RecordBlock u start len)
    (hRight : c ≤ start) :
    RecordBlock v start len := by
  apply recordBlock_preserved_of_equal_data B
  · intro j hjLe
    have hStop : c ≤ start + j := by
      exact hRight.trans (Nat.le_add_right start j)
    have hLeP : start + j ≤ p := by
      exact
        (Nat.add_le_add_left hjLe start).trans
          B.end_le_terminal
    exact R.height_eq_of_stop_le hStop hLeP
  · intro j hjLe
    have hStop : c ≤ start + j := by
      exact hRight.trans (Nat.le_add_right start j)
    have hLeP : start + j ≤ p := by
      exact
        (Nat.add_le_add_left hjLe start).trans
          B.end_le_terminal
    exact R.chordRankInt_outside hLeP (Or.inr hStop)

end RecordBlock

namespace InteriorRecordRun

/-- replacement 区間より完全に左にある連続 Record 区間はそのまま保存される。 -/
noncomputable def preserved_on_left
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (BRep : BlockReplacement u v a c)
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop)
    (hLeft : stop ≤ a) :
    InteriorRecordRun v start lengths stop := by
  induction R with
  | one B hInterior =>
      apply InteriorRecordRun.one
      · exact B.preserved_on_left BRep (by omega)
      · exact hInterior
  | @cons start len stop rest B hInterior T ih =>
      apply InteriorRecordRun.cons
      · exact B.preserved_on_left BRep (by
          have hTailEnd := T.start_add_sum_eq_stop
          have hTailPos := T.sum_pos
          omega)
      · exact hInterior
      · exact ih hLeft

/-- replacement 区間より完全に右にある連続 Record 区間も保存される。 -/
noncomputable def preserved_on_right
    {p H a c : ℕ}
    {u v : FiberPoint p H}
    (BRep : BlockReplacement u v a c)
    {start stop : ℕ}
    {lengths : List ℕ}
    (R : InteriorRecordRun u start lengths stop)
    (hRight : c ≤ start) :
    InteriorRecordRun v start lengths stop := by
  induction R with
  | one B hInterior =>
      apply InteriorRecordRun.one
      · exact B.preserved_on_right BRep hRight
      · exact hInterior
  | @cons start len stop rest B hInterior T ih =>
      apply InteriorRecordRun.cons
      · exact B.preserved_on_right BRep hRight
      · exact hInterior
      · exact ih (by omega)

end InteriorRecordRun

end RecordFerrers
end Collatz2
