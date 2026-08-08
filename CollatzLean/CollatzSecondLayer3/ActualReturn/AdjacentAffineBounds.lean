import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentGeometry
import CollatzLean.CollatzSecondLayer3.ActualReturn.Arithmetic
import CollatzLean.CollatzSecondLayer3.ContractingWindowBounds

/-!
# adjacent return の sharp affine bounds

旧 first-crossing 算術で得た prefix weighted bound を Adjacent Expanding Return へ
再接続する。また、次 future-minimum へ向かう contracting suffix 群から
affine constant の双対的な sharp 上界を導く。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord

/-- 非空 suffix を先頭から順にすべて contracting とする再帰的性質。 -/
def AllSuffixesContracting : ExpWord → Prop
  | [] => True
  | e :: w => Contracting (e :: w) ∧ AllSuffixesContracting w

/--
actual segment の各開始 offset から終点までが contracting なら、
その exponent word は `AllSuffixesContracting`。
-/
theorem allSuffixesContracting_segment
    (O : OddOrbit)
    {i q : ℕ}
    (h : ∀ k : ℕ, k < q →
      Contracting (O.segmentWord (i + k) (q - k))) :
    AllSuffixesContracting (O.segmentWord i q) := by
  induction q generalizing i with
  | zero =>
      simp [AllSuffixesContracting]
  | succ q ih =>
      rw [O.segmentWord_succ]
      constructor
      · have h0 := h 0 (by omega)
        simpa using h0
      · apply ih (i := i + 1)
        intro k hk
        have hs := h (k + 1) (by omega)
        have hindex : i + (k + 1) = i + 1 + k := by omega
        have hlen : (q + 1) - (k + 1) = q - k := by omega
        rw [hindex, hlen] at hs
        exact hs

/--
cons語全体がcontractingなら、
affineConstのhead項に必要な評価を得る。
-/
private theorem contracting_cons_head_bound
    {e : ℕ}
    {w : ExpWord}
    (hWhole : Contracting (e :: w)) :
    3 * 3 ^ oddSteps w <
      2 ^ (e + twoSteps w) := by
  unfold Contracting at hWhole
  simpa [pow_succ, Nat.mul_comm] using hWhole


/--
tailのsharp評価を`2^e`倍して、
cons語のtail項に必要なscaleへ移す。
-/
private theorem three_mul_affineConst_tail_scaled
    (e : ℕ)
    {w : ExpWord}
    (hi :
      3 * affineConst w <
        w.length * 2 ^ twoSteps w) :
    3 * (2 ^ e * affineConst w) <
      w.length * 2 ^ (e + twoSteps w) := by
  have hpowPos : 0 < 2 ^ e :=
    Nat.pow_pos (by omega : 0 < (2 : ℕ))
  have hmul :
      2 ^ e * (3 * affineConst w) <
        2 ^ e * (w.length * 2 ^ twoSteps w) :=
    (Nat.mul_lt_mul_left hpowPos).2 hi
  simpa [
    pow_add,
    Nat.mul_assoc,
    Nat.mul_comm,
    Nat.mul_left_comm
  ] using hmul


/--
cons語に対する算術帰納step。

whole contractingによるhead評価と、
tailのsharp評価を合わせる。
-/
private theorem three_mul_affineConst_cons_step
    {e : ℕ}
    {w : ExpWord}
    (hWhole : Contracting (e :: w))
    (hi :
      3 * affineConst w <
        w.length * 2 ^ twoSteps w) :
    3 * affineConst (e :: w) <
      (e :: w).length * 2 ^ twoSteps (e :: w) := by
  have hHead :
      3 * 3 ^ oddSteps w <
        2 ^ (e + twoSteps w) :=
    contracting_cons_head_bound hWhole
  have hTailScaled :
      3 * (2 ^ e * affineConst w) <
        w.length * 2 ^ (e + twoSteps w) :=
    three_mul_affineConst_tail_scaled e hi
  calc
    3 * affineConst (e :: w)
        =
          3 * 3 ^ oddSteps w +
            3 * (2 ^ e * affineConst w) := by
      simp [affineConst, oddSteps]
      ring
    _ <
        2 ^ (e + twoSteps w) +
          w.length * 2 ^ (e + twoSteps w) := by
      omega
    _ =
        (e :: w).length *
          2 ^ twoSteps (e :: w) := by
      simp only [List.length_cons, twoSteps_cons]
      ring


/--
全非空 suffix が contracting な非空語では
`3 * B < length * 2^H`。
-/
theorem three_mul_affineConst_lt_length_mul_twoPow
    {w : ExpWord}
    (hne : w ≠ [])
    (hAll : AllSuffixesContracting w) :
    3 * affineConst w <
      w.length * 2 ^ twoSteps w := by
  revert hne hAll
  induction w with
  | nil =>
      intro hne _
      exact False.elim (hne rfl)
  | cons e w ih =>
      intro _ hAll
      change
        Contracting (e :: w) ∧
          AllSuffixesContracting w
        at hAll
      rcases hAll with ⟨hWhole, hTail⟩
      by_cases hw : w = []
      · subst w
        simpa [
          Contracting,
          oddSteps,
          twoSteps,
          affineConst
        ] using hWhole
      · have hi :
            3 * affineConst w <
              w.length * 2 ^ twoSteps w :=
          ih hw hTail
        exact
          three_mul_affineConst_cons_step
            hWhole hi

/-- proper prefix expanding だけで first-crossing 用 weighted prefix bound を得る。 -/
theorem weightedPrefixBound_of_properPrefixesExpanding
    {w : ExpWord}
    (h : ProperPrefixesExpanding w) :
    WeightedPrefixBound 1 1 w := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp only [List.take_zero, twoSteps_nil, pow_zero, mul_one, Std.le_refl]
  · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
    have hExp : Expanding (w.take j) := h j hjPos hj
    have hodd : oddSteps (w.take j) = j :=
      oddSteps_take_eq (Nat.le_of_lt hj)
    unfold Expanding at hExp
    simpa [WeightedPrefixBound, hodd] using Nat.le_of_lt hExp

end ExpWord

namespace AdjacentContractingReturnData

/-- adjacent contracting window の正差を既存 WindowDifferenceData として束ねる。 -/
noncomputable def windowDifference
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    O.WindowDifferenceData D.state.startIndex D.state.length := by
  apply O.windowDifferenceData_of_lt
  have hnext :
      O.value (D.state.startIndex + D.state.length) = D.state.nextValue := by
    rw [← D.state.nextIndex_eq_startIndex_add_length]
    rfl
  rw [hnext, D.state.nextValue_eq_startValue_add_valueGap]
  unfold AdjacentFutureMinimumReturnData.startValue
  exact Nat.lt_add_of_pos_right D.state.valueGap_pos

/-- WindowDifferenceData の `2^depth * oddPart` は adjacent 値差そのもの。 -/
theorem windowDifference_eq_valueGap
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    2 ^ D.windowDifference.depth * D.windowDifference.oddPart =
      D.state.valueGap := by
  have hd := D.windowDifference.difference
  have hv :
      O.value (D.state.startIndex + D.state.length) =
        O.value D.state.startIndex + D.state.valueGap := by
    rw [← D.state.nextIndex_eq_startIndex_add_length]
    simpa [AdjacentFutureMinimumReturnData.nextValue,
      AdjacentFutureMinimumReturnData.startValue] using
      D.state.nextValue_eq_startValue_add_valueGap
  omega

/-- 既存 contracting-window 資産: `2^H * Δ < B`。 -/
theorem twoPow_totalExponent_mul_valueGap_lt_affineConstant
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    2 ^ D.state.totalExponent * D.state.valueGap <
      D.state.affineConstant := by
  have hcontractWord :
      3 ^ D.state.length <
        2 ^ D.state.word.twoSteps :=
    D.contracting_inequality
  have hcontract :
      3 ^ D.state.length <
        2 ^ O.windowTwoSteps D.state.startIndex D.state.length := by
    change
      3 ^ D.state.length <
        2 ^
          (O.segmentWord
            D.state.startIndex
            D.state.length).twoSteps
    change
      3 ^ D.state.length <
        2 ^
          (O.segmentWord
            D.state.startIndex
            D.state.length).twoSteps
      at hcontractWord
    simpa [OddOrbit.windowTwoSteps] using hcontractWord
  have h :=
    OddOrbit.WindowDifferenceData.windowTwoPow_mul_gap_lt_segmentAffineConst
      D.windowDifference hcontract
  rw [D.windowDifference_eq_valueGap] at h
  change
    2 ^ D.state.word.twoSteps * D.state.valueGap <
      D.state.word.affineConst
    at h
  change
    2 ^ D.state.word.twoSteps * D.state.valueGap <
      D.state.word.affineConst
  exact h

/-- 既存 contracting-window 資産: `2^r * Δ < 3^r`。 -/
theorem twoPow_length_mul_valueGap_lt_threePow
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    2 ^ D.state.length * D.state.valueGap <
      3 ^ D.state.length := by
  have hcontractWord :
      3 ^ D.state.length <
        2 ^ D.state.word.twoSteps :=
    D.contracting_inequality
  have hcontract :
      3 ^ D.state.length <
        2 ^ O.windowTwoSteps D.state.startIndex D.state.length := by
    change
      3 ^ D.state.length <
        2 ^
          (O.segmentWord
            D.state.startIndex
            D.state.length).twoSteps
    change
      3 ^ D.state.length <
        2 ^
          (O.segmentWord
            D.state.startIndex
            D.state.length).twoSteps
      at hcontractWord
    simpa [OddOrbit.windowTwoSteps] using hcontractWord
  have h :=
    OddOrbit.WindowDifferenceData.twoPow_length_mul_gap_lt_threePow
      D.windowDifference hcontract
  rw [D.windowDifference_eq_valueGap] at h
  exact h
/-- whole を含む全 suffix が contracting。 -/
theorem allSuffixesContracting
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    ExpWord.AllSuffixesContracting D.state.word := by
  change
    ExpWord.AllSuffixesContracting
      (O.segmentWord D.state.startIndex D.state.length)
  apply ExpWord.allSuffixesContracting_segment O
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    have hConWord : Contracting D.state.word := by
      simpa [
        AdjacentContractingReturnAt,
        AdjacentFutureMinimumReturnData.word
      ] using D.contracting
    change
      Contracting
        (O.segmentWord D.state.startIndex D.state.length)
      at hConWord
    exact hConWord
  · exact
      D.state.properSuffix_contracting
        (Nat.pos_of_ne_zero hk0) hk

/--
Adjacent Contracting Return の sharp affine budget。
`3B < r * 2^H`。
-/
theorem three_mul_affineConstant_lt_length_mul_twoPow
    {O : OddOrbit}
    (D : AdjacentContractingReturnData O) :
    3 * D.state.affineConstant <
      D.state.length * 2 ^ D.state.totalExponent := by
  have h :=
    ExpWord.three_mul_affineConst_lt_length_mul_twoPow
      D.state.word_nonempty D.allSuffixesContracting
  simpa [AdjacentFutureMinimumReturnData.affineConstant,
    AdjacentFutureMinimumReturnData.totalExponent] using h

end AdjacentContractingReturnData

namespace AdjacentExpandingReturnData

/-- proper-prefix expanding から sharp first-crossing 型 affine 上界を再利用する。 -/
theorem affineConstant_le_length_mul_threePow_pred
    {O : OddOrbit}
    (D : AdjacentExpandingReturnData O) :
    D.state.affineConstant ≤
      D.state.length * 3 ^ (D.state.length - 1) := by
  have hPrefix : WeightedPrefixBound 1 1 D.state.word :=
    ExpWord.weightedPrefixBound_of_properPrefixesExpanding
      D.properPrefixesExpanding
  have h :=
    ExpWord.weighted_affineConst_le_sharp
      D.state.word 1 1 hPrefix
  simpa [AdjacentFutureMinimumReturnData.affineConstant] using h

/--
長さ2以上の Adjacent Expanding Return では、先頭を除いた actual tail の
全非空 suffix が contracting。
-/
theorem tail_allSuffixesContracting
    {O : OddOrbit}
    (D : AdjacentExpandingReturnData O)
    (hlen : 1 < D.state.length) :
    ExpWord.AllSuffixesContracting
      (O.segmentWord (D.state.startIndex + 1) (D.state.length - 1)) := by
  apply ExpWord.allSuffixesContracting_segment O
  intro k hk
  have hkWhole : k + 1 < D.state.length := by omega
  have hs :=
    D.state.properSuffix_contracting
      (k := k + 1) (by omega) hkWhole
  have hindex :
      D.state.startIndex + (k + 1) =
        D.state.startIndex + 1 + k := by omega
  have hlenEq :
      D.state.length - (k + 1) =
        (D.state.length - 1) - k := by omega
  rw [hindex, hlenEq] at hs
  exact hs

/--
Adjacent Expanding Return の suffix 側 sharp affine budget。

先頭 exponent は exact 1 なので、長さ2以上では
`3B < 3^r + (r-1) * 2^H`。
-/
theorem three_mul_affineConstant_lt_threePow_add_tail_twoPow
    {O : OddOrbit}
    (D : AdjacentExpandingReturnData O)
    (hlen : 1 < D.state.length) :
    3 * D.state.affineConstant <
      3 ^ D.state.length +
        (D.state.length - 1) * 2 ^ D.state.totalExponent := by
  let tail : ExpWord :=
    O.segmentWord (D.state.startIndex + 1) (D.state.length - 1)
  have htailNe : tail ≠ [] := by
    intro hnil
    have hlen0 := congrArg List.length hnil
    dsimp [tail] at hlen0
    simp at hlen0
    omega
  have htailAll : ExpWord.AllSuffixesContracting tail := by
    simpa [tail] using D.tail_allSuffixesContracting hlen
  have htailBound :
      3 * affineConst tail < tail.length * 2 ^ twoSteps tail :=
    ExpWord.three_mul_affineConst_lt_length_mul_twoPow htailNe htailAll
  have hword := D.state.word_eq_startExponent_cons_tail
  have hstartExp := D.state.startExponent_eq_one
  have hword' : D.state.word = 1 :: tail := by
    simpa [tail, hstartExp] using hword
  have htailLength : tail.length = D.state.length - 1 := by
    simp [tail]
  have hH : D.state.totalExponent = twoSteps tail + 1 := by
    unfold AdjacentFutureMinimumReturnData.totalExponent
    rw [hword']
    simp [Nat.add_comm]
  have hB :
      D.state.affineConstant =
        3 ^ (D.state.length - 1) + 2 * affineConst tail := by
    unfold AdjacentFutureMinimumReturnData.affineConstant
    rw [hword']
    simp [htailLength, oddSteps]
  have hscaled :
      3 * (2 * affineConst tail) <
        (D.state.length - 1) * 2 ^ D.state.totalExponent := by
    have hmul :=
      (Nat.mul_lt_mul_left (by omega : 0 < (2 : ℕ))).2 htailBound
    rw [hH, pow_succ]
    simpa [htailLength, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  rw [hB]
  have hpow :
      3 * 3 ^ (D.state.length - 1) =
        3 ^ D.state.length := by
    have hlenOne : 1 ≤ D.state.length :=
      Nat.le_of_lt hlen
    calc
      3 * 3 ^ (D.state.length - 1)
          = 3 ^ (D.state.length - 1) * 3 := by ring
      _ = 3 ^ ((D.state.length - 1) + 1) := by
            rw [pow_succ]
      _ = 3 ^ D.state.length := by
            rw [Nat.sub_add_cancel hlenOne]
  omega

/--
全 consecutive proper-prefix pair に既存 `7/4` bound を適用する。
-/
theorem prefixPair_seven_fourths_bound
    {O : OddOrbit}
    (D : AdjacentExpandingReturnData O)
    {j : ℕ}
    (hj : 0 < j)
    (hnext : j + 1 < D.state.length) :
    4 *
        (3 * 2 ^ O.windowTwoSteps D.state.startIndex j +
          2 ^
            (O.windowTwoSteps D.state.startIndex j +
              O.exponent (D.state.startIndex + j))) <
      7 * 3 ^ (j + 1) := by
  have hjWord : j < D.state.word.length := by
    rw [D.state.word_length]
    omega
  have hj1Word : j + 1 < D.state.word.length := by
    rw [D.state.word_length]
    exact hnext
  have hE0 := D.properPrefixesExpanding j hj hjWord
  have hE1 := D.properPrefixesExpanding (j + 1) (by omega) hj1Word
  have hjLe : j ≤ D.state.length := by omega
  have hj1Le : j + 1 ≤ D.state.length := by omega
  rw [D.state.word_take_eq_segmentWord hjLe] at hE0
  rw [D.state.word_take_eq_segmentWord hj1Le] at hE1
  have h0 :
      2 ^ O.windowTwoSteps D.state.startIndex j < 3 ^ j := by
    simpa [OddOrbit.windowTwoSteps, Expanding, oddSteps] using hE0
  have h1raw :
      2 ^ O.windowTwoSteps D.state.startIndex (j + 1) <
        3 ^ (j + 1) := by
    simpa [OddOrbit.windowTwoSteps, Expanding, oddSteps] using hE1
  have hlast := O.windowTwoSteps_succ_last D.state.startIndex j
  have h1 :
      2 ^
          (O.windowTwoSteps D.state.startIndex j +
            O.exponent (D.state.startIndex + j)) <
        3 ^ (j + 1) := by
    rw [hlast] at h1raw
    exact h1raw
  exact CollatzSecondLayer3.prefixPair_seven_fourths_bound
    (O.exponent_pos (D.state.startIndex + j)) h0 h1

end AdjacentExpandingReturnData

end CollatzSecondLayer3
