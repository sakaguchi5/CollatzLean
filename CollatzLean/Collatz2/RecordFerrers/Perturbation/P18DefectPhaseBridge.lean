import CollatzLean.Collatz2.RecordFerrers.Perturbation.P17FirstFundamentalStripReturn

/-!
# Record–Ferrers 摂動理論 18: 欠陥位相と修復位相の橋

P09–P10 では、隣接長さ移送による一ビット欠陥について

* 欠陥が生じるかどうかは候補二長自身の `criticalCarry r' s'`
* 欠陥が左か右かは開始位置 `a` から候補 middle cut までの `criticalCarry a r'`
* 欠陥位置は局所 boundary excess の位置と正確に一致

まで分解した。

一方 P14–P17 では、primitive + StripReduced の fixed-chord 幾何において

* roof contact = clearance の飽和
* roof contact = `extraDepth = 0`
* canonical repair cut = fundamental rank strip への最初の復帰

まで得られている。

このファイルでは両者を同じ「位相」言語へ移す。
実数回転はまだ導入せず、repair 側では有限剰余

  (H * k) % p

を repair phase とする。proper cut の chord rank は

  chordRank(k) = repairPhase(k) + p * extraDepth(k)

と正確に分解されるので、repair は

  chordRank(k) = repairPhase(k)

という剰余位相への復帰として読める。

欠陥側では `criticalCarry a r'` を左右位置を決める二値位相として取り出す。
最後に、局所 carry 欠陥と geometric saturation の組を、
「欠陥側の二値位相 + repair 側の剰余位相」へ lossless に翻訳する。

注意: このファイル単独では `AdjacentLengthTransfer` を actual `FiberPoint` deformation と同一視しない。
`r',s'` はここでは候補二分割の長さ座標である。
source の genuine adjacent `RecordBlock`、actual `BlockReplacement u v`、target middle cut `k`
から `AdjacentLengthTransfer` を導出し、一ビット欠陥を actual depth / P19 admissibility へ戻す
realization bridge は P21 で与える。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
primitive/reduced chord `(p,H)` の cut `k` における有限剰余位相。
proper cut では Christoffel strip rank そのものになる。
-/
def repairPhase
    (P : Word.ContractingExponentPair)
    (k : ℕ) : ℕ :=
  (P.twoDepth * k) % P.oddCount

/-- repair phase は常に denominator 未満。 -/
theorem repairPhase_lt_oddCount
    (P : Word.ContractingExponentPair)
    (k : ℕ) :
    repairPhase P k < P.oddCount := by
  unfold repairPhase
  exact Nat.mod_lt _ P.oddCount_pos

/--
primitive + StripReduced の proper cut では、pair 側の strip rank は repair phase そのもの。
-/
theorem pairStripRank_eq_repairPhase_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    P.stripRank k = repairPhase P k := by
  simpa [repairPhase] using
    P.stripRank_eq_twoDepth_mul_mod_of_primitive_reduced
      hPrimitive hReduced hkPos hkLt

/--
同じ fixed chord を持つ任意の `FiberPoint` でも deterministic strip rank は repair phase に一致する。
-/
theorem wordStripRank_eq_repairPhase_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    stripRank v.word k = repairPhase P k := by
  have hPair :=
    P.stripRank_eq_twoDepth_mul_mod_of_primitive_reduced
      hPrimitive hReduced hkPos hkLt
  unfold Word.ContractingExponentPair.stripRank at hPair
  unfold Word.stripRank repairPhase
  rw [v.twoSteps_eq, v.oddSteps_eq]
  exact hPair

/--
primitive + StripReduced FirstCrossing target の proper cut では、
chord rank は「有限剰余位相 + denominator × Ferrers depth」に正確に分解される。
-/
theorem chordRank_eq_repairPhase_add_oddCount_mul_extraDepth
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    chordRank v.word k =
      repairPhase P k +
        P.oddCount * extraDepth v.word k := by
  have hkLtWord : k < oddSteps v.word := by
    rw [v.oddSteps_eq]
    exact hkLt
  have hDecomp :=
    hF.chordRank_eq_stripRank_add_extraDepth hkPos hkLtWord
  have hStrip :=
    wordStripRank_eq_repairPhase_of_primitiveReduced
      P hPrimitive hReduced v hkPos hkLt
  rw [hStrip, v.oddSteps_eq] at hDecomp
  exact hDecomp

/--
rank path が deterministic repair phase まで下り切ったこと。
これは repair 側の有限位相接触条件である。
-/
def RepairPhaseContact
    (P : Word.ContractingExponentPair)
    (v : FiberPoint P.oddCount P.twoDepth)
    (k : ℕ) : Prop :=
  chordRank v.word k = repairPhase P k

/--
proper cut では repair phase への接触と `extraDepth = 0` が正確に同値。
有限剰余部分を引いた残りが `p * extraDepth` だけだからである。
-/
theorem repairPhaseContact_iff_extraDepth_eq_zero_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    RepairPhaseContact P v k ↔
      extraDepth v.word k = 0 := by
  have hDecomp :=
    chordRank_eq_repairPhase_add_oddCount_mul_extraDepth
      P hPrimitive hReduced v hF hkPos hkLt
  constructor
  · intro hContact
    unfold RepairPhaseContact at hContact
    have hEq :
        repairPhase P k +
            P.oddCount * extraDepth v.word k =
          repairPhase P k + 0 := by
      calc
        repairPhase P k + P.oddCount * extraDepth v.word k
            = chordRank v.word k := hDecomp.symm
        _ = repairPhase P k := hContact
        _ = repairPhase P k + 0 := by simp
    have hMulZero :
        P.oddCount * extraDepth v.word k = 0 :=
      Nat.add_left_cancel hEq
    rcases Nat.mul_eq_zero.mp hMulZero with hOddZero | hExtraZero
    · exact False.elim (Nat.ne_of_gt P.oddCount_pos hOddZero)
    · exact hExtraZero
  · intro hExtraZero
    unfold RepairPhaseContact
    simpa [hExtraZero] using hDecomp

/--
primitive + StripReduced proper cut では、critical roof への接触と repair phase への接触が同値。
-/
theorem roofContact_iff_repairPhaseContact_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    RoofContact v k ↔ RepairPhaseContact P v k := by
  calc
    RoofContact v k ↔ extraDepth v.word k = 0 :=
      roofContact_iff_extraDepth_eq_zero v hF hkPos hkLt
    _ ↔ RepairPhaseContact P v k :=
      (repairPhaseContact_iff_extraDepth_eq_zero_of_primitiveReduced
        P hPrimitive hReduced v hF hkPos hkLt).symm

/--
P14 の clearance 飽和条件を repair phase だけで読み直す。
source から target への profile displacement が source clearance を使い切ることと、
target chord rank が有限剰余位相へ戻ることは正確に同値。
-/
theorem displacement_eq_clearance_iff_repairPhaseContact
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (hFv : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    profileDisplacement u v k = criticalDefectInt u k ↔
      RepairPhaseContact P v k := by
  calc
    profileDisplacement u v k = criticalDefectInt u k ↔ RoofContact v k :=
      (roofContact_iff_displacement_eq_clearance u v k).symm
    _ ↔ RepairPhaseContact P v k :=
      roofContact_iff_repairPhaseContact_of_primitiveReduced
        P hPrimitive hReduced v hFv hkPos hkLt

namespace RepairCut

/-- canonical repair cut 自身は repair phase に接触する。 -/
theorem repairPhaseContact
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k : ℕ}
    (R : RepairCut v after k) :
    RepairPhaseContact P v k := by
  have hkPos : 0 < k := by
    have hAfter := R.after_lt
    omega
  exact
    (roofContact_iff_repairPhaseContact_of_primitiveReduced
      P hPrimitive hReduced v hF hkPos R.proper).1
      R.contact

/--
canonical repair cut は `after` より後で repair phase に初めて接触する cut。
P17 の fundamental-strip first return を equality 位相の言葉へ sharpen した形。
-/
theorem firstRepairPhaseContact
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k : ℕ}
    (R : RepairCut v after k) :
    RepairPhaseContact P v k ∧
      ∀ j : ℕ,
        after < j →
        j < k →
        ¬ RepairPhaseContact P v j := by
  refine ⟨R.repairPhaseContact hPrimitive hReduced hF, ?_⟩
  intro j hAfter hBefore hPhase
  have hjPos : 0 < j := by
    omega
  have hjLt : j < P.oddCount :=
    lt_trans hBefore R.proper
  have hRoof : RoofContact v j :=
    (roofContact_iff_repairPhaseContact_of_primitiveReduced
      P hPrimitive hReduced v hF hjPos hjLt).2 hPhase
  exact R.no_earlier_contact hAfter hBefore hRoof

end RepairCut

/--
一ビット欠陥が発生したとき、その欠陥が左か右かを決める二値位相。
0 は左欠陥、1 は右欠陥に対応する。
-/
def defectSidePhase
    (a r : ℕ) : ℕ :=
  criticalCarry a r

/-- 欠陥側位相は必ず 0 または 1。 -/
theorem defectSidePhase_eq_zero_or_one
    (a r : ℕ) :
    defectSidePhase a r = 0 ∨ defectSidePhase a r = 1 := by
  unfold defectSidePhase
  exact criticalCarry_eq_zero_or_one a r

/--
局所 carry が 0 と分かっているとき、欠陥側位相 0 は左欠陥と正確に同値。
-/
theorem adjacentTransfer_leftCarryDefect_iff_defectSidePhase_zero
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hLocal : criticalCarry r' s' = 0) :
    LeftCarryDefect a r' s' ↔ defectSidePhase a r' = 0 := by
  simpa [defectSidePhase] using
    adjacentTransfer_leftCarryDefect_iff_leftCarry_zero
      hOld T hLocal

/--
局所 carry が 0 と分かっているとき、欠陥側位相 1 は右欠陥と正確に同値。
-/
theorem adjacentTransfer_rightCarryDefect_iff_defectSidePhase_one
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hLocal : criticalCarry r' s' = 0) :
    RightCarryDefect a r' s' ↔ defectSidePhase a r' = 1 := by
  simpa [defectSidePhase] using
    adjacentTransfer_rightCarryDefect_iff_leftCarry_one
      hOld T hLocal

/--
欠陥側の二値位相と、その左右に現れる局所 boundary excess を一つの条件にまとめる。
-/
def DefectPhaseExcessDichotomy
    (a r s : ℕ) : Prop :=
  (defectSidePhase a r = 0 ∧
      Skeleton.boundaryExcessInt a [r] = 1 ∧
      Skeleton.boundaryExcessInt (a + r) [s] = 0) ∨
    (defectSidePhase a r = 1 ∧
      Skeleton.boundaryExcessInt a [r] = 0 ∧
      Skeleton.boundaryExcessInt (a + r) [s] = 1)

/--
全長保存移送後の局所 carry が 0 になることは、
「二値位相が欠陥の左右を選び、その側だけ局所 excess が 1 になる」ことと正確に同値。

欠陥の存在は `criticalCarry r' s'` だけで決まり、
欠陥の位置は `defectSidePhase a r'` が決める、という分離を一つの定理にまとめたもの。
-/
theorem adjacentTransfer_localCarry_zero_iff_defectPhaseExcessDichotomy
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    criticalCarry r' s' = 0 ↔
      DefectPhaseExcessDichotomy a r' s' := by
  constructor
  · intro hLocal
    have hDefect :=
      (adjacentTransfer_localCarry_zero_iff_left_or_right_defect
        hOld T).1 hLocal
    rcases hDefect with hLeft | hRight
    · left
      have hPhase : defectSidePhase a r' = 0 :=
        (adjacentTransfer_leftCarryDefect_iff_defectSidePhase_zero
          hOld T hLocal).1 hLeft
      have hExcess :=
        (Skeleton.leftCarryDefect_iff_localBoundaryExcess
          a r' s').1 hLeft
      exact ⟨hPhase, hExcess.1, hExcess.2⟩
    · right
      have hPhase : defectSidePhase a r' = 1 :=
        (adjacentTransfer_rightCarryDefect_iff_defectSidePhase_one
          hOld T hLocal).1 hRight
      have hExcess :=
        (Skeleton.rightCarryDefect_iff_localBoundaryExcess
          a r' s').1 hRight
      exact ⟨hPhase, hExcess.1, hExcess.2⟩
  · intro hPhaseExcess
    rcases hPhaseExcess with hLeft | hRight
    · have hLeftDefect : LeftCarryDefect a r' s' :=
        (Skeleton.leftCarryDefect_iff_localBoundaryExcess
          a r' s').2 ⟨hLeft.2.1, hLeft.2.2⟩
      exact
        (adjacentTransfer_localCarry_zero_iff_left_or_right_defect
          hOld T).2 (Or.inl hLeftDefect)
    · have hRightDefect : RightCarryDefect a r' s' :=
        (Skeleton.rightCarryDefect_iff_localBoundaryExcess
          a r' s').2 ⟨hRight.2.1, hRight.2.2⟩
      exact
        (adjacentTransfer_localCarry_zero_iff_left_or_right_defect
          hOld T).2 (Or.inr hRightDefect)

/--
P18 の結合定理。

左辺は

* 隣接長さ移送が一ビット欠陥を作ること
* fixed-chord deformation が cut `k` で source clearance を使い切ること

を同時に述べる。

右辺ではそれらを

* 欠陥側の二値位相 + 左右 boundary excess
* repair 側の有限剰余位相への接触

へ完全に翻訳する。

この定理は二つの観測条件の lossless な座標変換であり、
隣接長さ移送と `u -> v` の具体的 realization を新たに仮定・主張するものではない。
-/
theorem adjacentDefect_and_saturation_iff_phaseBridge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (hFv : FirstCrossing v.word)
    {a r s r' s' k : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    (criticalCarry r' s' = 0 ∧
      profileDisplacement u v k = criticalDefectInt u k) ↔
    (DefectPhaseExcessDichotomy a r' s' ∧
      RepairPhaseContact P v k) := by
  constructor
  · rintro ⟨hDefect, hSat⟩
    refine ⟨?_, ?_⟩
    · exact
        (adjacentTransfer_localCarry_zero_iff_defectPhaseExcessDichotomy
          hOld T).1 hDefect
    · exact
        (displacement_eq_clearance_iff_repairPhaseContact
          P hPrimitive hReduced u v hFv hkPos hkLt).1 hSat
  · rintro ⟨hDefectPhase, hRepairPhase⟩
    refine ⟨?_, ?_⟩
    · exact
        (adjacentTransfer_localCarry_zero_iff_defectPhaseExcessDichotomy
          hOld T).2 hDefectPhase
    · exact
        (displacement_eq_clearance_iff_repairPhaseContact
          P hPrimitive hReduced u v hFv hkPos hkLt).2 hRepairPhase

end RecordFerrers
end Collatz2
