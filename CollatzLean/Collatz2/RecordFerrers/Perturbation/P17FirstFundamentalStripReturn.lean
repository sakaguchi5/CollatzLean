import CollatzLean.Collatz2.RecordFerrers.Perturbation.P16PrimitiveReducedChristoffelRepair

/-!
# Record–Ferrers 摂動理論 17: first fundamental-strip return

P15 の canonical repair cut と P16 の primitive + reduced Christoffel 座標化を、
rank quotient / fundamental strip の first-return 言語へ変換する。

proper FirstCrossing cut では

* `RoofContact v k ↔ extraDepth v.word k = 0`
* primitive + StripReduced では `rankQuotient = extraDepth`
* したがって `RoofContact v k ↔ rankQuotient v.word k = 0`
* quotient が zero であることは `chordRank v.word k < p` と同値

となる。

よって canonical repair cut は、壊れた旧 boundary `after` より後で
rank path が fundamental strip `[0,p)` へ初めて戻る cut そのものである。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
fixed denominator `p` に対する fundamental rank strip。

`chordRank < p`、すなわち rank quotient が zero の層を表す。
-/
def FundamentalRankStrip
    (P : Word.ContractingExponentPair)
    (v : FiberPoint P.oddCount P.twoDepth)
    (k : ℕ) : Prop :=
  chordRank v.word k < P.oddCount

/--
FirstCrossing proper cut では roof contact は extra depth が zero であることと同値。
-/
theorem roofContact_iff_extraDepth_eq_zero
    {p H : ℕ}
    (v : FiberPoint p H)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < p) :
    RoofContact v k ↔
      extraDepth v.word k = 0 := by
  have hkLtWord : k < oddSteps v.word := by
    rw [v.oddSteps_eq]
    exact hkLt
  have hLe :
      prefixTwoDepth v.word k ≤ criticalHeight k :=
    hF.prefixTwoDepth_le_criticalHeight hkPos hkLtWord
  unfold RoofContact FiberPoint.height extraDepth
  omega

/--
primitive + StripReduced では proper deterministic strip が一周未満なので、
rank quotient は pure Ferrers depth `extraDepth` そのものになる。

既存の current-A specialization ではなく、任意の fixed-chord `FiberPoint` に対する版。
-/
theorem rankQuotient_eq_extraDepth_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    rankQuotient v.word k =
      extraDepth v.word k := by
  have hkLtWord : k < oddSteps v.word := by
    rw [v.oddSteps_eq]
    exact hkLt
  have hPair :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hkPos hkLt
  have hStripLt :
      stripRank v.word k < oddSteps v.word := by
    have h := hPair.2
    unfold Word.ContractingExponentPair.stripRank at h
    unfold Word.stripRank
    rw [v.twoSteps_eq, v.oddSteps_eq]
    exact h
  have hEq :=
    hF.rankQuotient_eq_stripDiv_add_extraDepth
      hkPos hkLtWord
  rw [Nat.div_eq_of_lt hStripLt, zero_add] at hEq
  exact hEq

/--
primitive + StripReduced の proper FirstCrossing cut では、
critical roof への接触と rank quotient zero が exact に同値。
-/
theorem roofContact_iff_rankQuotient_eq_zero_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    RoofContact v k ↔
      rankQuotient v.word k = 0 := by
  have hQ :=
    rankQuotient_eq_extraDepth_of_primitiveReduced
      P hPrimitive hReduced v hF hkPos hkLt
  rw [hQ]
  exact
    roofContact_iff_extraDepth_eq_zero
      v hF hkPos hkLt

/--
primitive + StripReduced の proper FirstCrossing cut では、
roof contact は chord rank が fundamental strip `[0,p)` に入ることと同値。
-/
theorem roofContact_iff_chordRank_lt_oddCount_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    RoofContact v k ↔
      chordRank v.word k < P.oddCount := by
  have hRoofQ :=
    roofContact_iff_rankQuotient_eq_zero_of_primitiveReduced
      P hPrimitive hReduced v hF hkPos hkLt
  constructor
  · intro hRoof
    have hQZero : rankQuotient v.word k = 0 :=
      hRoofQ.1 hRoof
    have hDecomp :=
      chordRank_eq_rankResidue_add_oddSteps_mul_rankQuotient
        v.word k
    have hResidLt :=
      hF.rankResidue_lt_oddSteps (k := k)
    rw [hQZero, mul_zero, add_zero] at hDecomp
    rw [hDecomp]
    rw [v.oddSteps_eq] at hResidLt
    exact hResidLt
  · intro hRankLt
    have hRankLtWord :
        chordRank v.word k < oddSteps v.word := by
      rw [v.oddSteps_eq]
      exact hRankLt
    have hQZero :
        rankQuotient v.word k = 0 := by
      unfold rankQuotient
      exact Nat.div_eq_of_lt hRankLtWord
    exact hRoofQ.2 hQZero

/--
primitive + StripReduced では proper roof contact と
fundamental rank strip membership が exact に同値。
-/
theorem roofContact_iff_fundamentalRankStrip_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    RoofContact v k ↔
      FundamentalRankStrip P v k := by
  unfold FundamentalRankStrip
  exact
    roofContact_iff_chordRank_lt_oddCount_of_primitiveReduced
      P hPrimitive hReduced v hF hkPos hkLt

/-- 二つの cut index の右向き距離。 -/
def repairDisplacement
    (after k : ℕ) : ℕ :=
  k - after

namespace RepairCut

/-- canonical repair cut までの repair displacement は正。 -/
theorem repairDisplacement_pos
    {p H after k : ℕ}
    {v : FiberPoint p H}
    (R : RepairCut v after k) :
    0 < repairDisplacement after k := by
  unfold repairDisplacement
  exact Nat.sub_pos_of_lt R.after_lt

/-- repair displacement を旧 boundary に足すと repair cut に到達する。 -/
theorem after_add_repairDisplacement
    {p H after k : ℕ}
    {v : FiberPoint p H}
    (R : RepairCut v after k) :
    after + repairDisplacement after k = k := by
  unfold repairDisplacement
  have hAfterLt : after < k :=
    R.after_lt
  omega

/--
repair cut より前には target の roof contact は存在しない。
P15 の `least` を roof-contact 言語で直接使う補助定理。
-/
theorem no_earlier_contact
    {p H after k : ℕ}
    {v : FiberPoint p H}
    (R : RepairCut v after k)
    {j : ℕ}
    (hAfter : after < j)
    (hBefore : j < k) :
    ¬ RoofContact v j := by
  intro hRoof
  have hProper : j < p :=
    lt_trans hBefore R.proper
  have hCandidate :
      RepairCandidate v after j :=
    ⟨hAfter, hProper, hRoof⟩
  have hLeast := R.least j hCandidate
  omega

/-- canonical repair cut 自身では rank quotient が zero。 -/
theorem rankQuotient_eq_zero
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k : ℕ}
    (R : RepairCut v after k) :
    rankQuotient v.word k = 0 := by
  have hkPos : 0 < k := by
    have hAfter := R.after_lt
    omega
  exact
    (roofContact_iff_rankQuotient_eq_zero_of_primitiveReduced
      P hPrimitive hReduced v hF hkPos R.proper).1
      R.contact

/--
canonical repair cut より前の全 cut では rank quotient は strict positive。
したがって zero section への復帰は repair cut が最初。
-/
theorem rankQuotient_pos_before
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k j : ℕ}
    (R : RepairCut v after k)
    (hAfter : after < j)
    (hBefore : j < k) :
    0 < rankQuotient v.word j := by
  have hjPos : 0 < j := by
    omega
  have hjLt : j < P.oddCount :=
    lt_trans hBefore R.proper
  have hNotRoof :
      ¬ RoofContact v j :=
    R.no_earlier_contact hAfter hBefore
  have hIff :=
    roofContact_iff_rankQuotient_eq_zero_of_primitiveReduced
      P hPrimitive hReduced v hF hjPos hjLt
  have hNe :
      rankQuotient v.word j ≠ 0 := by
    intro hZero
    exact hNotRoof (hIff.2 hZero)
  exact Nat.pos_of_ne_zero hNe

/-- canonical repair cut 自身の chord rank は fundamental strip `[0,p)` 内。 -/
theorem chordRank_lt_oddCount
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k : ℕ}
    (R : RepairCut v after k) :
    chordRank v.word k < P.oddCount := by
  have hkPos : 0 < k := by
    have hAfter := R.after_lt
    omega
  exact
    (roofContact_iff_chordRank_lt_oddCount_of_primitiveReduced
      P hPrimitive hReduced v hF hkPos R.proper).1
      R.contact

/--
canonical repair cut より前では chord rank は denominator 以上。
つまり fundamental strip `[0,p)` にはまだ戻っていない。
-/
theorem oddCount_le_chordRank_before
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k j : ℕ}
    (R : RepairCut v after k)
    (hAfter : after < j)
    (hBefore : j < k) :
    P.oddCount ≤ chordRank v.word j := by
  have hjPos : 0 < j := by
    omega
  have hjLt : j < P.oddCount :=
    lt_trans hBefore R.proper
  have hNotRoof :
      ¬ RoofContact v j :=
    R.no_earlier_contact hAfter hBefore
  by_contra hnot
  have hRankLt :
      chordRank v.word j < P.oddCount := by
    omega
  have hRoof :
      RoofContact v j :=
    (roofContact_iff_chordRank_lt_oddCount_of_primitiveReduced
      P hPrimitive hReduced v hF hjPos hjLt).2
      hRankLt
  exact hNotRoof hRoof

/--
canonical repair cut は rank quotient の最初の zero。

これは `repair = zero section への first return` という P17 の quotient 版。
-/
theorem firstRankQuotientZero
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k : ℕ}
    (R : RepairCut v after k) :
    rankQuotient v.word k = 0 ∧
      ∀ j : ℕ,
        after < j →
        j < k →
        0 < rankQuotient v.word j := by
  refine ⟨R.rankQuotient_eq_zero hPrimitive hReduced hF, ?_⟩
  intro j hAfter hBefore
  exact
    R.rankQuotient_pos_before
      hPrimitive hReduced hF hAfter hBefore

/--
P17 主定理。

primitive + StripReduced FirstCrossing target では canonical repair cut は、
壊れた旧 boundary `after` より後で rank path が fundamental strip `[0,p)` へ
初めて戻る cut そのものである。
-/
theorem firstFundamentalStripReturn
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {after k : ℕ}
    (R : RepairCut v after k) :
    FundamentalRankStrip P v k ∧
      ∀ j : ℕ,
        after < j →
        j < k →
        ¬ FundamentalRankStrip P v j := by
  constructor
  · unfold FundamentalRankStrip
    exact
      R.chordRank_lt_oddCount
        hPrimitive hReduced hF
  · intro j hAfter hBefore
    unfold FundamentalRankStrip
    have hLower :=
      R.oddCount_le_chordRank_before
        hPrimitive hReduced hF hAfter hBefore
    omega

end RepairCut

end RecordFerrers
end Collatz2
