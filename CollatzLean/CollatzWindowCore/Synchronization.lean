import CollatzLean.CollatzWindowCore.Analysis



/-!
# ordered q-windowの最小同期境界

初期差深さが消費総指数を超えている間、上下二値は同じ指数語をactual replayする。
差深さへ初めて到達する直前を選び、`PreparedWindowPacket`を自動構成する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord.Runs

/-- actual orbit値から始まるrunは同じ長さのorbit segmentに一致する。 -/
theorem eq_segment_of_orbit_start
    {O : OddOrbit} {w : ExpWord} {i z : ℕ}
    (h : Runs w (O.value i) z) :
    w = O.segmentWord i w.length ∧
      z = O.value (i + w.length) := by
  induction w generalizing i z with
  | nil =>
      cases h with
      | nil => simp
  | cons e w ih =>
      cases h with
      | @cons _ _ _ y _ he hstep hy htail =>
          have hOrbitStep :
              2 ^ O.exponent i * O.value (i + 1) =
                3 * O.value i + 1 :=
            O.step i
          have hunique :=
            OddOrbit.next_data_unique hstep hOrbitStep hy (O.value_odd (i + 1))
          rcases hunique with ⟨heq, hyeq⟩
          subst e
          subst y
          obtain ⟨hword, hend⟩ := ih (i := i + 1) (z := z) htail
          constructor
          · simp only [List.length_cons, OddOrbit.segmentWord_succ]
            congr 1
          · rw [hend]
            congr 1
            simp [Nat.add_comm, Nat.add_left_comm]


end ExpWord.Runs

namespace OddOrbit

namespace WindowDifferenceData

/-- 二つのodd軌道値の正差に現れる完全2進深さは正。 -/
theorem depth_pos
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    0 < D.depth := by
  by_contra hnot
  have hzero : D.depth = 0 := by omega
  rcases O.value_odd i with ⟨a, ha⟩
  rcases D.oddPart_odd with ⟨b, hb⟩
  have heven : Even (O.value (i + q)) := by
    refine ⟨a + b + 1, ?_⟩
    rw [D.difference, hzero, ha, hb]
    norm_num
    ring
  exact odd_even_false_nat (O.value_odd (i + q)) heven

end WindowDifferenceData

/-- segmentを末尾へ一文字伸ばしたときの総2除算数。 -/
theorem windowTwoSteps_succ_last
    (O : OddOrbit) (i k : ℕ) :
    O.windowTwoSteps i (k + 1) =
      O.windowTwoSteps i k + O.exponent (i + k) := by
  have h := congrArg twoSteps (O.segmentWord_add i k 1)
  rw [twoSteps_append] at h
  simpa [windowTwoSteps] using h


/-- ordered差深さへ一文字越えて到達する有限長が存在する。 -/
theorem synchronizationBoundary_exists
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    ∃ k : ℕ,
      D.depth ≤ O.windowTwoSteps i (k + 1) := by
  refine ⟨D.depth, ?_⟩
  have hvalid := (O.runs_segment i (D.depth + 1)).valid
  have hlen := oddSteps_le_twoSteps hvalid
  have hsteps :
      D.depth + 1 ≤ O.windowTwoSteps i (D.depth + 1) := by
    simpa [windowTwoSteps, oddSteps] using hlen
  omega

/-- ordered差深さへ初めて到達する直前の長さ。 -/
noncomputable def synchronizationBoundaryLength
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) : ℕ :=
  Nat.find (synchronizationBoundary_exists D)

/-- 境界を一文字越えれば差深さ以上を消費する。 -/
theorem synchronizationBoundaryLength_spec
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    D.depth ≤
      O.windowTwoSteps i (synchronizationBoundaryLength D + 1) := by
  unfold synchronizationBoundaryLength
  exact Nat.find_spec (synchronizationBoundary_exists D)

/-- 境界語自身の消費量はまだ差深さ未満。 -/
theorem synchronizationBoundaryLength_consumed_lt
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    O.windowTwoSteps i (synchronizationBoundaryLength D) < D.depth := by
  unfold synchronizationBoundaryLength
  cases hk : Nat.find (synchronizationBoundary_exists D) with
  | zero =>
      simpa [windowTwoSteps] using D.depth_pos
  | succ m =>
      have hmLt : m < Nat.find (synchronizationBoundary_exists D) := by
        omega
      have hnot :
          ¬ D.depth ≤ O.windowTwoSteps i (m + 1) :=
        Nat.find_min (synchronizationBoundary_exists D) hmLt
      exact Nat.lt_of_not_ge hnot

/-- 未消費差深さは境界直後のlower指数以下。 -/
theorem synchronizationBoundary_remaining_le_next
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    D.depth - O.windowTwoSteps i (synchronizationBoundaryLength D) ≤
      O.exponent (i + synchronizationBoundaryLength D) := by
  have hs := synchronizationBoundaryLength_spec D
  rw [O.windowTwoSteps_succ_last] at hs
  omega

/-- ordered windowから自動構成されたprepared boundary data。 -/
structure SynchronizedPreparationData
    (O : OddOrbit) (i q : ℕ) where
  original : WindowDifferenceData O i q
  boundaryLength : ℕ
  lowerWord : ExpWord
  lowerWord_eq : lowerWord = O.segmentWord i boundaryLength
  upperWord_eq : lowerWord = O.segmentWord (i + q) boundaryLength
  packet : PreparedWindowPacket O (i + boundaryLength) q

/-- ordered actual windowを最小同期境界まで進めてprepared packetを得る。 -/
noncomputable def prepareWindow
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q)
    (hq : 0 < q) :
    SynchronizedPreparationData O i q := by
  let k := synchronizationBoundaryLength D
  let w := O.segmentWord i k
  let lowerFinish := O.value (i + k)
  let remaining := D.depth - O.windowTwoSteps i k
  let newOdd := 3 ^ oddSteps w * D.oddPart
  let upperPred := lowerFinish + 2 ^ remaining * newOdd
  have hconsumed : O.windowTwoSteps i k < D.depth := by
    simpa [k] using synchronizationBoundaryLength_consumed_lt D
  have hlowerRun : Runs w (O.value i) lowerFinish := by
    simpa [w, lowerFinish] using O.runs_segment i k
  have hreplay0 :
      Runs w
        (O.value i + 2 ^ D.depth * D.oddPart)
        upperPred := by
    dsimp [upperPred, lowerFinish, remaining, newOdd]
    simpa [windowTwoSteps, w, Nat.mul_assoc] using
      hlowerRun.runs_replay_of_gap_depth_gt_twoSteps
        (u := D.oddPart)
        hconsumed
  have hreplay : Runs w (O.value (i + q)) upperPred := by
    rw [D.difference]
    exact hreplay0
  have hactual := ExpWord.Runs.eq_segment_of_orbit_start hreplay
  have hwordLen : w.length = k := by simp [w]
  have hupperWord : w = O.segmentWord (i + q) k := by
    simpa [hwordLen] using hactual.1
  have hupperFinish : upperPred = O.value (i + q + k) := by
    simpa [hwordLen] using hactual.2
  have hodd : Odd newOdd := by
    dsimp [newOdd]
    exact
      (show Odd (3 ^ oddSteps w) by
        exact (show Odd (3 : ℕ) by decide).pow).mul D.oddPart_odd
  have hdifference :
      O.value ((i + k) + q) =
        O.value (i + k) + 2 ^ remaining * newOdd := by
    calc
      O.value ((i + k) + q) = O.value (i + q + k) := by
        congr 1
        omega
      _ = upperPred := hupperFinish.symm
      _ = O.value (i + k) + 2 ^ remaining * newOdd := by
        rfl
  let D' : WindowDifferenceData O (i + k) q :=
    { depth := remaining
      oddPart := newOdd
      difference := hdifference
      oddPart_odd := hodd }
  have hdepthLe : remaining ≤ O.exponent (i + k) := by
    simpa [k, remaining] using synchronizationBoundary_remaining_le_next D
  let P : PreparedWindowPacket O (i + k) q :=
    { toWindowDifferenceData := D'
      length_pos := hq
      depth_le_nextExponent := hdepthLe }
  exact
    { original := D
      boundaryLength := k
      lowerWord := w
      lowerWord_eq := rfl
      upperWord_eq := hupperWord
      packet := P }


/-- 任意のordered actual windowを同期準備後の有限四分岐へ送る。 -/
theorem orderedWindowAnalysis_nonempty
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q)
    (hq : 0 < q) :
    let S := prepareWindow D hq
    Nonempty
      (PreparedWindowAlternative S.packet ⊕
        SpecialC3At O (i + S.boundaryLength) q) := by
  dsimp
  exact preparedWindowAnalysis_nonempty (prepareWindow D hq).packet

end OddOrbit
end CollatzSecondLayer2
