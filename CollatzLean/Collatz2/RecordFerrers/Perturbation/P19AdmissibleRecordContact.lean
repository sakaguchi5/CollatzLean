import CollatzLean.Collatz2.RecordFerrers.Perturbation.P18DefectPhaseBridge
import CollatzLean.Collatz2.RecordFerrers.Factorization.PrimitiveReducedInverse

/-!
# Record–Ferrers 摂動理論 19: genuine record 接触と terminal 吸収

P15–P18 の `RepairCut` は「最初の critical roof 接触」を記録する幾何学的対象である。
しかし genuine な interior record endpoint には、roof 接触だけでは足りない。
anchor `a` から endpoint `k` までの長さ `k-a` に対して

  criticalCarry a (k-a) = 1

が必要である。

そこで本ファイルでは

* roof 接触
* anchor-relative carry = 1

を同時に満たす proper cut を `AdmissibleRecordContact` と定義する。
さらに、その最初の接触までの local word が `MinimalBlock` になり、
genuine `RecordBlock` へ昇格することを示す。

一方、そのような proper contact が一つも存在しない場合は、
anchor から terminal までの suffix 全体が一つの terminal `RecordBlock` になる。

従って primitive + StripReduced の FirstCrossing fiber では、
正の roof anchor から必ず次の genuine record block が存在する。

重要: P19 は target-side の定理層である。
`v : FiberPoint p H`、`FirstCrossing v.word`、roof anchor がすでに与えられた後の
record eligibility / existence を扱い、source deformation や `AdjacentLengthTransfer` の
実現方法は前提に含めない。actual `BlockReplacement` と target middle cut から
P19 の admissibility へ入る realization bridge は P21 が担当する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
`anchor` より後の genuine interior record endpoint 候補。

単なる roof 接触に加えて、anchor-relative critical carry が 1 であることを要求する。
この定義だけで `RecordBlock` を主張するわけではなく、最初の admissible contact と
FirstCrossing 条件を組み合わせて後続 theorem で genuine block へ昇格する。
-/
def AdmissibleRecordContact
    {p H : ℕ}
    (v : FiberPoint p H)
    (anchor k : ℕ) : Prop :=
  anchor < k ∧
    k < p ∧
    RoofContact v anchor ∧
    RoofContact v k ∧
    criticalCarry anchor (k - anchor) = 1

/-- admissible contact の中で最初のもの。 -/
structure FirstAdmissibleRecordContact
    {p H : ℕ}
    (v : FiberPoint p H)
    (anchor k : ℕ) : Prop where
  candidate : AdmissibleRecordContact v anchor k
  least :
    ∀ j : ℕ,
      AdmissibleRecordContact v anchor j →
      k ≤ j

namespace FirstAdmissibleRecordContact

/-- 最初の admissible contact は anchor より真に後ろ。 -/
theorem anchor_lt
    {p H anchor k : ℕ}
    {v : FiberPoint p H}
    (F : FirstAdmissibleRecordContact v anchor k) :
    anchor < k :=
  F.candidate.1

/-- 最初の admissible contact は terminal より手前。 -/
theorem proper
    {p H anchor k : ℕ}
    {v : FiberPoint p H}
    (F : FirstAdmissibleRecordContact v anchor k) :
    k < p :=
  F.candidate.2.1

/-- 左 anchor 自身は critical roof 上にある。 -/
theorem anchor_contact
    {p H anchor k : ℕ}
    {v : FiberPoint p H}
    (F : FirstAdmissibleRecordContact v anchor k) :
    RoofContact v anchor :=
  F.candidate.2.2.1

/-- 最初の admissible endpoint は critical roof 上にある。 -/
theorem contact
    {p H anchor k : ℕ}
    {v : FiberPoint p H}
    (F : FirstAdmissibleRecordContact v anchor k) :
    RoofContact v k :=
  F.candidate.2.2.2.1

/-- anchor から最初の admissible endpoint までの carry は 1。 -/
theorem carry_one
    {p H anchor k : ℕ}
    {v : FiberPoint p H}
    (F : FirstAdmissibleRecordContact v anchor k) :
    criticalCarry anchor (k - anchor) = 1 :=
  F.candidate.2.2.2.2

/-- 最初の admissible contact より前には別の admissible contact はない。 -/
theorem no_earlier
    {p H anchor k : ℕ}
    {v : FiberPoint p H}
    (F : FirstAdmissibleRecordContact v anchor k)
    {j : ℕ}
    (hBefore : j < k) :
    ¬ AdmissibleRecordContact v anchor j := by
  intro hCandidate
  have hLeast := F.least j hCandidate
  omega

end FirstAdmissibleRecordContact

/--
primitive + StripReduced では、admissible contact の roof 条件を
P18 の有限剰余位相への接触へそのまま置き換えられる。
-/
theorem admissibleRecordContact_iff_repairPhaseContact_and_carry
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor k : ℕ} :
    AdmissibleRecordContact v anchor k ↔
      anchor < k ∧
        k < P.oddCount ∧
        RoofContact v anchor ∧
        RepairPhaseContact P v k ∧
        criticalCarry anchor (k - anchor) = 1 := by
  constructor
  · intro h
    rcases h with ⟨hAK, hkLt, hRoofA, hRoofK, hCarry⟩
    have hkPos : 0 < k := by omega
    have hPhase : RepairPhaseContact P v k :=
      (roofContact_iff_repairPhaseContact_of_primitiveReduced
        P hPrimitive hReduced v hF hkPos hkLt).1 hRoofK
    exact ⟨hAK, hkLt, hRoofA, hPhase, hCarry⟩
  · rintro ⟨hAK, hkLt, hRoofA, hPhase, hCarry⟩
    have hkPos : 0 < k := by omega
    have hRoofK : RoofContact v k :=
      (roofContact_iff_repairPhaseContact_of_primitiveReduced
        P hPrimitive hReduced v hF hkPos hkLt).2 hPhase
    exact ⟨hAK, hkLt, hRoofA, hRoofK, hCarry⟩

/--
primitive + StripReduced pair では、任意の proper cut `a` とその補長 `p-a` に対して

  criticalHeight a + criticalHeight (p-a) + 1 = H

が成り立つ。

proper strip rank `r(a), r(p-a)` はともに `1,...,p-1` にあり、
二つの Euclidean remainder の和は `p` になるためである。
この恒等式が terminal absorption の exact depth を与える。
-/
theorem criticalHeight_add_complement_add_one_eq_twoDepth_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {a : ℕ}
    (haPos : 0 < a)
    (haLt : a < P.oddCount) :
    criticalHeight a +
        criticalHeight (P.oddCount - a) + 1 =
      P.twoDepth := by
  have hsPos : 0 < P.oddCount - a := by omega
  have hsLt : P.oddCount - a < P.oddCount := by omega
  have hRangeA :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced haPos haLt
  have hRangeS :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hsPos hsLt
  have hLowerA := P.criticalHeight_below_chord haPos
  have hLowerS := P.criticalHeight_below_chord hsPos
  have hDecompA :
      P.stripRank a +
          P.oddCount * criticalHeight a =
        P.twoDepth * a := by
    unfold Word.ContractingExponentPair.stripRank
    omega
  have hDecompS :
      P.stripRank (P.oddCount - a) +
          P.oddCount * criticalHeight (P.oddCount - a) =
        P.twoDepth * (P.oddCount - a) := by
    unfold Word.ContractingExponentPair.stripRank
    omega
  have hAP : a + (P.oddCount - a) = P.oddCount := by
    omega
  have hEq :
      P.stripRank a +
          P.stripRank (P.oddCount - a) +
          P.oddCount *
            (criticalHeight a +
              criticalHeight (P.oddCount - a)) =
        P.oddCount * P.twoDepth := by
    calc
      P.stripRank a +
          P.stripRank (P.oddCount - a) +
          P.oddCount *
            (criticalHeight a +
              criticalHeight (P.oddCount - a))
          =
        (P.stripRank a +
            P.oddCount * criticalHeight a) +
          (P.stripRank (P.oddCount - a) +
            P.oddCount * criticalHeight (P.oddCount - a)) := by
              ring
      _ =
        P.twoDepth * a +
          P.twoDepth * (P.oddCount - a) := by
            rw [hDecompA, hDecompS]
      _ = P.twoDepth * P.oddCount := by
            rw [← hAP]
            ring_nf
            simp
      _ = P.oddCount * P.twoDepth := by ring
  have hRankSumPos :
      0 < P.stripRank a + P.stripRank (P.oddCount - a) := by
    omega
  have hRankSumLt :
      P.stripRank a + P.stripRank (P.oddCount - a) <
        2 * P.oddCount := by
    omega
  have hMulLt :
      P.oddCount *
          (criticalHeight a + criticalHeight (P.oddCount - a)) <
        P.oddCount * P.twoDepth := by
    omega
  have hCritSumLt :
      criticalHeight a + criticalHeight (P.oddCount - a) <
        P.twoDepth :=
    (Nat.mul_lt_mul_left P.oddCount_pos).1 hMulLt
  let d : ℕ :=
    P.twoDepth -
      (criticalHeight a + criticalHeight (P.oddCount - a))
  have hdPos : 0 < d := by
    dsimp [d]
    omega
  have hHSplit :
      P.twoDepth =
        (criticalHeight a + criticalHeight (P.oddCount - a)) + d := by
    dsimp [d]
    omega
  have hEqD :
      P.stripRank a + P.stripRank (P.oddCount - a) =
        P.oddCount * d := by
    have hEq' :
        P.oddCount *
              (criticalHeight a + criticalHeight (P.oddCount - a)) +
            (P.stripRank a + P.stripRank (P.oddCount - a)) =
          P.oddCount *
              (criticalHeight a + criticalHeight (P.oddCount - a)) +
            P.oddCount * d := by
      calc
        P.oddCount *
              (criticalHeight a + criticalHeight (P.oddCount - a)) +
            (P.stripRank a + P.stripRank (P.oddCount - a))
            =
          P.stripRank a + P.stripRank (P.oddCount - a) +
            P.oddCount *
              (criticalHeight a + criticalHeight (P.oddCount - a)) := by
                ring
        _ = P.oddCount * P.twoDepth := hEq
        _ =
          P.oddCount *
            ((criticalHeight a + criticalHeight (P.oddCount - a)) + d) := by
              rw [hHSplit]
        _ =
          P.oddCount *
              (criticalHeight a + criticalHeight (P.oddCount - a)) +
            P.oddCount * d := by
              ring
    exact Nat.add_left_cancel hEq'
  have hMulDLt : P.oddCount * d < P.oddCount * 2 := by
    calc
      P.oddCount * d =
          P.stripRank a + P.stripRank (P.oddCount - a) :=
        hEqD.symm
      _ < 2 * P.oddCount := hRankSumLt
      _ = P.oddCount * 2 := by ring
  have hdLt : d < 2 :=
    (Nat.mul_lt_mul_left P.oddCount_pos).1 hMulDLt
  have hdEq : d = 1 := by omega
  rw [hHSplit, hdEq]

/--
roof anchor `anchor` から `stop` の手前まで admissible contact が存在しないなら、
`[anchor,stop)` の local block の全 proper prefix は local critical roof 以下にある。

もし local prefix が `criticalHeight j` を 1 段越えれば、
global FirstCrossing と critical carry の 0/1 性から
`anchor+j` が roof contact かつ carry 1 になり、admissible contact を作ってしまう。
-/
theorem localPrefix_le_of_no_admissible_before
    {p H : ℕ}
    (v : FiberPoint p H)
    (hF : FirstCrossing v.word)
    {anchor stop : ℕ}
    (hAnchorRoof : RoofContact v anchor)
    (hAnchorStop : anchor < stop)
    (hStopLe : stop ≤ p)
    (hNoBefore :
      ∀ m : ℕ,
        anchor < m →
        m < stop →
        ¬ AdmissibleRecordContact v anchor m)
    {j : ℕ}
    (hjPos : 0 < j)
    (hjLt : j < stop - anchor) :
    prefixTwoDepth
        (blockWord v anchor (stop - anchor)) j ≤
      criticalHeight j := by
  have hjLe : j ≤ stop - anchor := Nat.le_of_lt hjLt
  have hPrefixEq :
      prefixTwoDepth
          (blockWord v anchor (stop - anchor)) j =
        twoSteps (blockWord v anchor j) := by
    rw [prefixTwoDepth_blockWord v anchor (stop - anchor) j hjLe]
    rfl
  rw [hPrefixEq]
  by_contra hNot
  have hLocalGt :
      criticalHeight j < twoSteps (blockWord v anchor j) := by
    omega
  have hAJPos : 0 < anchor + j := by omega
  have hAJLtStop : anchor + j < stop := by omega
  have hAJLtP : anchor + j < p :=
    lt_of_lt_of_le hAJLtStop hStopLe
  have hAJLtWord : anchor + j < oddSteps v.word := by
    rw [v.oddSteps_eq]
    exact hAJLtP
  have hGlobalRaw :=
    hF.prefixTwoDepth_le_criticalHeight hAJPos hAJLtWord
  have hGlobal :
      v.height (anchor + j) ≤ criticalHeight (anchor + j) := by
    simpa [FiberPoint.height] using hGlobalRaw
  have hAdd := height_add_eq_add_blockDepth v anchor j
  have hCrit := criticalHeight_add_eq anchor j
  have hAnchorHeight := hAnchorRoof
  unfold RoofContact at hAnchorHeight
  have hCarryOne : criticalCarry anchor j = 1 := by
    rcases criticalCarry_eq_zero_or_one anchor j with hZero | hOne
    · rw [hZero] at hCrit
      omega
    · exact hOne
  have hRoofAJ : RoofContact v (anchor + j) := by
    unfold RoofContact
    rw [hCarryOne] at hCrit
    omega
  have hCandidate :
      AdmissibleRecordContact v anchor (anchor + j) := by
    refine ⟨by omega, hAJLtP, hAnchorRoof, hRoofAJ, ?_⟩
    simpa using hCarryOne
  exact hNoBefore (anchor + j) (by omega) hAJLtStop hCandidate

namespace FirstAdmissibleRecordContact

/--
最初の admissible contact までの local word は minimal FirstCrossing block。
-/
theorem local_minimalBlock
    {p H : ℕ}
    {v : FiberPoint p H}
    (hF : FirstCrossing v.word)
    {anchor k : ℕ}
    (F : FirstAdmissibleRecordContact v anchor k) :
    MinimalBlock (blockWord v anchor (k - anchor)) := by
  let len := k - anchor
  have hLenPos : 0 < len := by
    dsimp [len]
    exact Nat.sub_pos_of_lt F.candidate.1
  have hEndEq : anchor + len = k := by
    dsimp [len]
    omega
  have hEndLe : anchor + len ≤ p := by
    rw [hEndEq]
    exact Nat.le_of_lt F.proper
  have hOdd : oddSteps (blockWord v anchor len) = len :=
    oddSteps_blockWord v hEndLe
  have hAnchorRoof := F.anchor_contact
  have hEndRoof := F.contact
  unfold RoofContact at hAnchorRoof hEndRoof
  have hHeight := height_add_eq_add_blockDepth v anchor len
  have hCrit := criticalHeight_add_eq anchor len
  have hCarry : criticalCarry anchor len = 1 := by
    simpa [len] using F.carry_one
  rw [hEndEq, hAnchorRoof, hEndRoof] at hHeight
  rw [hCarry, hEndEq] at hCrit
  have hTerminalDepth :
      twoSteps (blockWord v anchor len) = criticalHeight len + 1 := by
    omega
  have hFirst : FirstCrossing (blockWord v anchor len) := by
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      have hPosOdd : 0 < oddSteps (blockWord v anchor len) := by
        rw [hOdd]
        exact hLenPos
      simpa [oddSteps] using hPosOdd
    · intro j hjPos hjLtWord
      have hjLt : j < len := by
        have hLenWord : (blockWord v anchor len).length = len := by
          simpa [oddSteps] using hOdd
        simpa [hLenWord] using hjLtWord
      have hDepth :
          prefixTwoDepth (blockWord v anchor len) j ≤ criticalHeight j := by
        apply localPrefix_le_of_no_admissible_before
          v hF F.anchor_contact F.anchor_lt (Nat.le_of_lt F.proper)
        · intro m hAM hMK
          exact F.no_earlier hMK
        · exact hjPos
        · simpa [len] using hjLt
      exact
        expanding_take_of_prefixTwoDepth_le_criticalHeight
          (blockWord v anchor len)
          hjPos
          (by
            rw [hOdd]
            exact Nat.le_of_lt hjLt)
          hDepth
    · apply contracting_of_twoSteps_eq_minimalDepth
      · rw [hOdd]
        exact hLenPos
      · unfold minimalDepth
        rw [hOdd]
        exact hTerminalDepth
  exact {
    firstCrossing := hFirst
    minimalDepth := by
      rw [hOdd]
      exact hTerminalDepth
  }

/--
最初の admissible contact は genuine interior `RecordBlock` endpoint になる。
-/
theorem toRecordBlock
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    (hF : FirstCrossing v.word)
    {anchor k : ℕ}
    (F : FirstAdmissibleRecordContact v anchor k) :
    RecordBlock v anchor (k - anchor) := by
  let len := k - anchor
  have hLenPos : 0 < len := by
    dsimp [len]
    exact Nat.sub_pos_of_lt F.candidate.1
  have hEndEq : anchor + len = k := by
    dsimp [len]
    omega
  have hEnd : anchor + len ≤ P.oddCount := by
    rw [hEndEq]
    exact Nat.le_of_lt F.proper
  have hLenLt : len < P.oddCount := by
    dsimp [len]
    exact lt_of_le_of_lt (Nat.sub_le k anchor) F.proper
  have hRange :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hLenPos hLenLt
  have hLower := P.criticalHeight_below_chord hLenPos
  have hStripLt :
      P.twoDepth * len -
          P.oddCount * criticalHeight len <
        P.oddCount := by
    simpa [Word.ContractingExponentPair.stripRank] using hRange.2
  have hDrop :
      P.twoDepth * len <
        P.oddCount * (criticalHeight len + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have M : MinimalBlock (blockWord v anchor len) := by
    simpa [len] using F.local_minimalBlock hF
  have hStartRoof := F.anchor_contact
  unfold RoofContact at hStartRoof
  apply RecordBlock.ofMinimalAtRoof
    v hLenPos hEnd M hStartRoof
  · intro j hjPos _hjLt
    exact P.criticalHeight_below_chord hjPos
  · exact hDrop
  · intro _hInterior
    have hRoof := F.contact
    unfold RoofContact at hRoof
    simpa [hEndEq] using hRoof

end FirstAdmissibleRecordContact

/--
proper admissible contact が一つもない場合、anchor から terminal までの suffix は
一つの minimal FirstCrossing block になる。
-/
theorem terminalMinimalBlock_of_no_admissible
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor)
    (hNo : ¬ ∃ k : ℕ, AdmissibleRecordContact v anchor k) :
    MinimalBlock
      (blockWord v anchor (P.oddCount - anchor)) := by
  let len := P.oddCount - anchor
  have hLenPos : 0 < len := by
    dsimp [len]
    omega
  have hEndEq : anchor + len = P.oddCount := by
    dsimp [len]
    omega
  have hEnd : anchor + len ≤ P.oddCount := by
    rw [hEndEq]
  have hOdd : oddSteps (blockWord v anchor len) = len :=
    oddSteps_blockWord v hEnd
  have hAnchorHeight := hAnchorRoof
  unfold RoofContact at hAnchorHeight
  have hHeight := height_add_eq_add_blockDepth v anchor len
  rw [hEndEq, v.height_terminal, hAnchorHeight] at hHeight
  have hComplement :=
    criticalHeight_add_complement_add_one_eq_twoDepth_of_primitiveReduced
      P hPrimitive hReduced hAnchorPos hAnchorLt
  have hTerminalDepth :
      twoSteps (blockWord v anchor len) = criticalHeight len + 1 := by
    dsimp [len] at hHeight hComplement ⊢
    omega
  have hFirst : FirstCrossing (blockWord v anchor len) := by
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      have hPosOdd : 0 < oddSteps (blockWord v anchor len) := by
        rw [hOdd]
        exact hLenPos
      simpa [oddSteps] using hPosOdd
    · intro j hjPos hjLtWord
      have hjLt : j < len := by
        have hLenWord : (blockWord v anchor len).length = len := by
          simpa [oddSteps] using hOdd
        simpa [hLenWord] using hjLtWord
      have hDepth :
          prefixTwoDepth (blockWord v anchor len) j ≤ criticalHeight j := by
        apply localPrefix_le_of_no_admissible_before
          v hF hAnchorRoof hAnchorLt (Nat.le_refl P.oddCount)
        · intro m hAM hMP hCandidate
          exact hNo ⟨m, hCandidate⟩
        · exact hjPos
        · simpa [len] using hjLt
      exact
        expanding_take_of_prefixTwoDepth_le_criticalHeight
          (blockWord v anchor len)
          hjPos
          (by
            rw [hOdd]
            exact Nat.le_of_lt hjLt)
          hDepth
    · apply contracting_of_twoSteps_eq_minimalDepth
      · rw [hOdd]
        exact hLenPos
      · unfold minimalDepth
        rw [hOdd]
        exact hTerminalDepth
  exact {
    firstCrossing := hFirst
    minimalDepth := by
      rw [hOdd]
      exact hTerminalDepth
  }

/--
proper admissible contact が存在しない場合、terminal までの suffix 全体が
genuine terminal `RecordBlock` になる。
-/
theorem terminalRecordBlock_of_no_admissible
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor)
    (hNo : ¬ ∃ k : ℕ, AdmissibleRecordContact v anchor k) :
    RecordBlock v anchor (P.oddCount - anchor) := by
  let len := P.oddCount - anchor
  have hLenPos : 0 < len := by
    dsimp [len]
    omega
  have hEndEq : anchor + len = P.oddCount := by
    dsimp [len]
    omega
  have hEnd : anchor + len ≤ P.oddCount := by
    rw [hEndEq]
  have hLenLt : len < P.oddCount := by
    dsimp [len]
    omega
  have hRange :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hLenPos hLenLt
  have hLower := P.criticalHeight_below_chord hLenPos
  have hStripLt :
      P.twoDepth * len -
          P.oddCount * criticalHeight len <
        P.oddCount := by
    simpa [Word.ContractingExponentPair.stripRank] using hRange.2
  have hDrop :
      P.twoDepth * len <
        P.oddCount * (criticalHeight len + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have M : MinimalBlock (blockWord v anchor len) := by
    simpa [len] using
      terminalMinimalBlock_of_no_admissible
        P hPrimitive hReduced v hF
        hAnchorPos hAnchorLt hAnchorRoof hNo
  have hStartRoof := hAnchorRoof
  unfold RoofContact at hStartRoof
  apply RecordBlock.ofMinimalAtRoof
    v hLenPos hEnd M hStartRoof
  · intro j hjPos _hjLt
    exact P.criticalHeight_below_chord hjPos
  · exact hDrop
  · intro hInterior
    rw [hEndEq] at hInterior
    omega

/--
P19 の exact 二分岐。

正の roof anchor から先は、

* 最初の admissible proper contact までの interior RecordBlock
* admissible proper contact が存在しない terminal absorption

のどちらかになる。
-/
theorem firstAdmissible_or_terminalRecordBlock_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor) :
    (∃ k : ℕ,
      FirstAdmissibleRecordContact v anchor k ∧
        RecordBlock v anchor (k - anchor)) ∨
      RecordBlock v anchor (P.oddCount - anchor) := by
  classical
  by_cases hExists :
      ∃ k : ℕ, AdmissibleRecordContact v anchor k
  · let k : ℕ := Nat.find hExists
    have hCandidate : AdmissibleRecordContact v anchor k :=
      Nat.find_spec hExists
    let F : FirstAdmissibleRecordContact v anchor k := {
      candidate := hCandidate
      least := by
        intro j hj
        exact Nat.find_min' hExists hj
    }
    exact Or.inl
      ⟨k, F, F.toRecordBlock hPrimitive hReduced hF⟩
  · exact Or.inr
      (terminalRecordBlock_of_no_admissible
        P hPrimitive hReduced v hF
        hAnchorPos hAnchorLt hAnchorRoof hExists)

/--
terminal absorption branch では anchor から terminal への critical carry は 0。
これは `RecordBlock` の terminal carry theorem から従う。
-/
theorem terminalCarry_zero_of_no_admissible
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor)
    (hNo : ¬ ∃ k : ℕ, AdmissibleRecordContact v anchor k) :
    criticalCarry anchor (P.oddCount - anchor) = 0 := by
  have B :=
    terminalRecordBlock_of_no_admissible
      P hPrimitive hReduced v hF
      hAnchorPos hAnchorLt hAnchorRoof hNo
  have hTerminal : anchor + (P.oddCount - anchor) = P.oddCount := by
    omega
  exact B.criticalCarry_eq_zero_of_terminal hTerminal hF

/--
P19 の一歩存在定理。

primitive + StripReduced FirstCrossing fiber の正の roof anchor からは、必ず
次の genuine `RecordBlock` が存在する。

* admissible proper contact があれば、その最初のものまでを interior block とする。
* 一つもなければ、terminal まで全部を一つの block とする。
-/
theorem exists_nextRecordBlock_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor) :
    ∃ len : ℕ, RecordBlock v anchor len := by
  classical
  by_cases hExists :
      ∃ k : ℕ, AdmissibleRecordContact v anchor k
  · let k : ℕ := Nat.find hExists
    have hCandidate : AdmissibleRecordContact v anchor k :=
      Nat.find_spec hExists
    let F : FirstAdmissibleRecordContact v anchor k := {
      candidate := hCandidate
      least := by
        intro j hj
        exact Nat.find_min' hExists hj
    }
    exact ⟨k - anchor, F.toRecordBlock hPrimitive hReduced hF⟩
  · exact
      ⟨P.oddCount - anchor,
        terminalRecordBlock_of_no_admissible
          P hPrimitive hReduced v hF
          hAnchorPos hAnchorLt hAnchorRoof hExists⟩

end RecordFerrers
end Collatz2
