import CollatzLean.Collatz2.CSTMicro.CarryGeometry.NormalizedDefectCrossing
import CollatzLean.Collatz2.Geometry.WeightedRankSum

/-!
# General CST: normalized defect -> weighted-rank small-residue bridge

`NormalizedDefectCrossing` までで actual first failure の upper coordinate

  q = normalizedSeparationDefectInt upper

は

  0 ≤ q < m

を満たすことが分かった。

一方 `Geometry/WeightedRankSum` は odd-only exponent word `Word = List ℕ` 上で

  3 * B = 3^m * weightedRankSum      (mod G)

を与える。

このファイルでは standard parity word を run-length で odd-only exponent word へ
lossless に圧縮し、first-passage upper word について

  oddSteps   = oddCount,
  twoSteps   = standard length,
  Word.B     = CSTMicro.B,
  terminalGap = CSTMicro terminal gap,

を証明する。さらに first-passage 性を odd-only `FirstCrossing` へ移す。

その上で normalized defect equation

  B = G * R + 2^k * q

を mod G に落とし、`2^k = 3^m (mod G)` と weighted-rank identity を結合して

  3*q = weightedRankSum              (mod G)

を得る。

既存 `RankUnitData` は primitive endpoint `gcd(k,m)=1` なら内部構成できる。
nonprimitive endpoint では root-unit の存在はこのファイルでは仮定せず、
既存 weighted-rank formalism の適用可能範囲を正確に分離する。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. standard parity word -> odd-only exponent word -/

/--
standard parity word の先頭 even-run と、その後の odd-only exponent word。

返り値 `(z,w)` の意味は

* `z` : 最初の odd bit より前にある leading even の個数
* `w` : 各 odd bit から次の odd bit（または terminal）までの standard step 数

である。`true` 自身が一回の `/2` を含むため、各 exponent は必ず `z+1 > 0`。
-/
def parityRunEncode : ParityWord → ℕ × Collatz2.Word
  | [] => (0, [])
  | false :: v =>
      let P := parityRunEncode v
      (P.1 + 1, P.2)
  | true :: v =>
      let P := parityRunEncode v
      (0, (P.1 + 1) :: P.2)

/-- leading even-run の長さ。 -/
def leadingEvenCount (v : ParityWord) : ℕ :=
  (parityRunEncode v).1

/-- standard parity word を odd-only exponent word へ圧縮したもの。 -/
def exponentWordOfParity (v : ParityWord) : Collatz2.Word :=
  (parityRunEncode v).2

@[simp] theorem leadingEvenCount_nil :
    leadingEvenCount ([] : ParityWord) = 0 := rfl

@[simp] theorem exponentWordOfParity_nil :
    exponentWordOfParity ([] : ParityWord) = [] := rfl

@[simp] theorem leadingEvenCount_false_cons (v : ParityWord) :
    leadingEvenCount (false :: v) = leadingEvenCount v + 1 := by
  rfl

@[simp] theorem exponentWordOfParity_false_cons (v : ParityWord) :
    exponentWordOfParity (false :: v) = exponentWordOfParity v := by
  rfl

@[simp] theorem leadingEvenCount_true_cons (v : ParityWord) :
    leadingEvenCount (true :: v) = 0 := by
  rfl

@[simp] theorem exponentWordOfParity_true_cons (v : ParityWord) :
    exponentWordOfParity (true :: v) =
      (leadingEvenCount v + 1) :: exponentWordOfParity v := by
  rfl

/--
leading even-run と exponent sum を足すと standard word length に戻る。
-/
theorem leadingEvenCount_add_twoSteps_exponentWordOfParity
    (v : ParityWord) :
    leadingEvenCount v + Collatz2.Word.twoSteps (exponentWordOfParity v) =
      v.length := by
  induction v with
  | nil =>
      simp
  | cons b v ih =>
      cases b
      · simp only [leadingEvenCount_false_cons, exponentWordOfParity_false_cons,
          List.length_cons]
        omega
      · simp only [leadingEvenCount_true_cons, exponentWordOfParity_true_cons,
          Collatz2.Word.twoSteps_cons, List.length_cons, zero_add]
        omega

/-- odd-only word の odd step 数は standard word の odd bit 数そのもの。 -/
theorem oddSteps_exponentWordOfParity
    (v : ParityWord) :
    Collatz2.Word.oddSteps (exponentWordOfParity v) = oddCount v := by
  induction v with
  | nil =>
      simp [Collatz2.Word.oddSteps, oddCount]
  | cons b v ih =>
      cases b
      · simp [ih, oddCount, bitNat]
      · simp [ih, oddCount, bitNat, Nat.add_comm]

/-- run encoder が作る exponent はすべて正。 -/
theorem exponentWordOfParity_valid
    (v : ParityWord) :
    Collatz2.Word.Valid (exponentWordOfParity v) := by
  induction v with
  | nil =>
      intro e he
      simp at he
  | cons b v ih =>
      cases b
      · simpa using ih
      · intro e he
        simp only [exponentWordOfParity_true_cons, List.mem_cons] at he
        rcases he with rfl | he
        · omega
        · exact ih e he

/--
standard affine numerator と odd-only affine numerator の lossless relation。
leading even が `z` 個あれば standard numerator は `2^z` 倍される。
-/
theorem affineConst_eq_twoPow_leading_mul_wordAffineConst
    (v : ParityWord) :
    affineConst v =
      2 ^ leadingEvenCount v *
        Collatz2.Word.affineConst (exponentWordOfParity v) := by
  induction v with
  | nil =>
      simp [affineConst]
  | cons b v ih =>
      cases b
      · simp only [affineConst_false_cons, leadingEvenCount_false_cons,
          exponentWordOfParity_false_cons]
        rw [ih, pow_succ]
        ring
      · simp only [affineConst_true_cons, leadingEvenCount_true_cons,
          exponentWordOfParity_true_cons, pow_zero, one_mul,
          Collatz2.Word.affineConst_cons]
        rw [oddSteps_exponentWordOfParity, ih, pow_succ]
        ring

/--
run boundary checkpoint。

`(z,w) = parityRunEncode v` とすると、先頭 `z` 個の even を飛ばし、
`w` の最初の `k` run を読み終えた standard time では odd count が exact に `k`。
-/
theorem prefixOddCount_at_exponent_checkpoint
    (v : ParityWord)
    (k : ℕ)
    (hk : k ≤ Collatz2.Word.oddSteps (exponentWordOfParity v)) :
    prefixOddCount v
        (leadingEvenCount v +
          Collatz2.Word.twoSteps ((exponentWordOfParity v).take k)) =
      k := by
  induction v generalizing k with
  | nil =>
      simp only [Word.oddSteps, exponentWordOfParity_nil, List.length_nil, nonpos_iff_eq_zero,
                  leadingEvenCount_nil,List.take_nil, Word.twoSteps_nil, add_zero,
                  prefixOddCount_zero] at hk ⊢
      exact hk.symm
  | cons b v ih =>
      cases b
      · have hk' :
            k ≤ Collatz2.Word.oddSteps (exponentWordOfParity v) := by
          simpa using hk
        have hih := ih k hk'
        have htime :
            leadingEvenCount v + 1 +
                Collatz2.Word.twoSteps ((exponentWordOfParity v).take k) =
              (leadingEvenCount v +
                Collatz2.Word.twoSteps ((exponentWordOfParity v).take k)) + 1 := by
          omega
        simp only [leadingEvenCount_false_cons, exponentWordOfParity_false_cons]
        rw [htime, prefixOddCount_cons_succ]
        simp [bitNat, hih]
      · by_cases hk0 : k = 0
        · subst k
          simp [prefixOddCount, oddCount]
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          have hj :
              j ≤ Collatz2.Word.oddSteps (exponentWordOfParity v) := by
            simp only [exponentWordOfParity_true_cons,
              Collatz2.Word.oddSteps_cons] at hk
            omega
          have hih := ih j hj
          have htime :
              leadingEvenCount v + 1 +
                  Collatz2.Word.twoSteps ((exponentWordOfParity v).take j) =
                (leadingEvenCount v +
                  Collatz2.Word.twoSteps ((exponentWordOfParity v).take j)) + 1 := by
            omega
          simp only [leadingEvenCount_true_cons, exponentWordOfParity_true_cons,
            List.take_succ_cons, Collatz2.Word.twoSteps_cons, zero_add]
          rw [htime, prefixOddCount_cons_succ]
          simp [bitNat, hih]
          ac_rfl

/-- valid word の proper take は総2指数を strict に減らす。 -/
theorem twoSteps_take_lt_of_valid
    {w : Collatz2.Word}
    (hvalid : Collatz2.Word.Valid w)
    {k : ℕ}
    (hk : k < Collatz2.Word.oddSteps w) :
    Collatz2.Word.twoSteps (w.take k) < Collatz2.Word.twoSteps w := by
  have hkLen : k < w.length := by
    simpa [Collatz2.Word.oddSteps] using hk
  have hdropNonempty : w.drop k ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [List.length_drop]
    omega
  have hwhole : Collatz2.Word.Valid (w.take k ++ w.drop k) := by
    simpa using hvalid
  have hdropValid : Collatz2.Word.Valid (w.drop k) :=
    hwhole.suffix
  have hdropPos : 0 < Collatz2.Word.twoSteps (w.drop k) :=
    Collatz2.Word.twoSteps_pos_of_valid_nonempty hdropValid hdropNonempty
  have hsum := Collatz2.Word.twoSteps_append (w.take k) (w.drop k)
  rw [List.take_append_drop] at hsum
  omega

/-- `1 < length` の first-passage word は必ず odd bit から始まる。 -/
theorem IsFirstPassageWord.exists_eq_true_cons
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    (hlen : 1 < v.length) :
    ∃ t : ParityWord, v = true :: t := by
  cases v with
  | nil =>
      simp at hlen
  | cons b t =>
      cases b
      · have hExp := h.2.1 1 (by omega) hlen
        norm_num [CoefficientExpandingAt, prefixOddCount, oddCount, bitNat] at hExp
      · exact ⟨t, rfl⟩

/-! ## 2. actual first-failure upper word as an odd-only FirstCrossing word -/

namespace FirstFailureEdge

/-- actual upper parity word の canonical odd-only run encoding。 -/
def upperExponentWord (F : FirstFailureEdge) : Collatz2.Word :=
  exponentWordOfParity F.step.edge.upperWord

/-- first-failure upper word の standard length は少なくとも 2。 -/
theorem one_lt_edge_upperWord_length
    (F : FirstFailureEdge) :
    1 < F.step.edge.upperWord.length := by
  rw [F.step.edge.upperWord_length]
  unfold AdjacentFerrersSwap.length
  omega

/-- actual upper first-passage word は `true` から始まる。 -/
theorem edge_upperWord_eq_true_cons
    (F : FirstFailureEdge) :
    ∃ t : ParityWord, F.step.edge.upperWord = true :: t := by
  exact
    F.edge_upper_firstPassage.exists_eq_true_cons
      F.one_lt_edge_upperWord_length

/-- actual upper word では leading even-run は zero。 -/
theorem leadingEvenCount_edge_upperWord_eq_zero
    (F : FirstFailureEdge) :
    leadingEvenCount F.step.edge.upperWord = 0 := by
  obtain ⟨t, ht⟩ := F.edge_upperWord_eq_true_cons
  rw [ht]
  simp

/-- encoded word の odd step 数は common odd total。 -/
@[simp] theorem upperExponentWord_oddSteps
    (F : FirstFailureEdge) :
    Collatz2.Word.oddSteps F.upperExponentWord = F.step.edge.oddTotal := by
  unfold upperExponentWord
  rw [oddSteps_exponentWordOfParity]
  simp

/-- encoded word の total two-depth は common standard length。 -/
@[simp] theorem upperExponentWord_twoSteps
    (F : FirstFailureEdge) :
    Collatz2.Word.twoSteps F.upperExponentWord = F.step.edge.length := by
  have hLen :=
    leadingEvenCount_add_twoSteps_exponentWordOfParity
      F.step.edge.upperWord
  rw [F.leadingEvenCount_edge_upperWord_eq_zero, zero_add] at hLen
  simpa [upperExponentWord] using hLen

/-- encoded word の affine numerator は standard parity numerator と exact に同じ。 -/
@[simp] theorem upperExponentWord_affineConst
    (F : FirstFailureEdge) :
    Collatz2.Word.affineConst F.upperExponentWord =
      affineConst F.step.edge.upperWord := by
  have hB :=
    affineConst_eq_twoPow_leading_mul_wordAffineConst
      F.step.edge.upperWord
  rw [F.leadingEvenCount_edge_upperWord_eq_zero] at hB
  simp only [pow_zero, one_mul] at hB
  simpa [upperExponentWord] using hB.symm

/-- encoded word は valid。 -/
theorem upperExponentWord_valid
    (F : FirstFailureEdge) :
    Collatz2.Word.Valid F.upperExponentWord := by
  unfold upperExponentWord
  exact exponentWordOfParity_valid _

/-- encoded word は nonempty。 -/
theorem upperExponentWord_nonempty
    (F : FirstFailureEdge) :
    F.upperExponentWord ≠ [] := by
  apply List.ne_nil_of_length_pos
  change 0 < Collatz2.Word.oddSteps F.upperExponentWord
  rw [F.upperExponentWord_oddSteps]
  exact F.edge_oddTotal_pos

/--
standard first-passage の proper expansion を run checkpoints へ制限すると、
encoded odd-only word の全 proper prefix determinant が positive。
-/
theorem upperExponentWord_properPositive
    (F : FirstFailureEdge) :
    Collatz2.Word.ProperPrefixesPositiveDeterminant F.upperExponentWord := by
  intro k hkPos hkLt
  let w := F.upperExponentWord
  have hvalid : Collatz2.Word.Valid w := by
    simpa [w] using F.upperExponentWord_valid
  have hkLtOdd : k < Collatz2.Word.oddSteps w := by
    simpa [Collatz2.Word.oddSteps] using hkLt
  have hkLe : k ≤ Collatz2.Word.oddSteps w := Nat.le_of_lt hkLtOdd
  have hCountRaw :=
    prefixOddCount_at_exponent_checkpoint
      F.step.edge.upperWord k (by simpa [w, upperExponentWord] using hkLe)
  have hCount :
      prefixOddCount F.step.edge.upperWord
          (Collatz2.Word.twoSteps (w.take k)) = k := by
    rw [F.leadingEvenCount_edge_upperWord_eq_zero, zero_add] at hCountRaw
    simpa [w, upperExponentWord] using hCountRaw
  have htakeValid : Collatz2.Word.Valid (w.take k) := by
    have hwhole : Collatz2.Word.Valid (w.take k ++ w.drop k) := by
      simpa using hvalid
    exact hwhole.prefix
  have htakeNonempty : w.take k ≠ [] := by
    apply List.ne_nil_of_length_pos
    have hkLen : k ≤ w.length := by
      simpa [Collatz2.Word.oddSteps] using hkLe
    rw [List.length_take_of_le hkLen]
    exact hkPos
  have htimePos : 0 < Collatz2.Word.twoSteps (w.take k) :=
    Collatz2.Word.twoSteps_pos_of_valid_nonempty htakeValid htakeNonempty
  have htimeLtWord :
      Collatz2.Word.twoSteps (w.take k) < Collatz2.Word.twoSteps w :=
    twoSteps_take_lt_of_valid hvalid hkLtOdd
  have htimeLt :
      Collatz2.Word.twoSteps (w.take k) < F.step.edge.upperWord.length := by
    calc
      Collatz2.Word.twoSteps (w.take k)
          < Collatz2.Word.twoSteps w := htimeLtWord
      _ = F.step.edge.length := by simp only [upperExponentWord_twoSteps, w]
      _ = F.step.edge.upperWord.length := by simp
  have hExp :=
    F.edge_upper_firstPassage.2.1
      (Collatz2.Word.twoSteps (w.take k)) htimePos htimeLt
  unfold CoefficientExpandingAt at hExp
  rw [hCount] at hExp
  change Collatz2.Word.Expanding (w.take k)
  apply (Collatz2.Word.expanding_iff_twoPow_lt_threePow).2
  have hkLen : k ≤ w.length := by
    simpa [Collatz2.Word.oddSteps] using hkLe
  have hOddTake : Collatz2.Word.oddSteps (w.take k) = k := by
    unfold Collatz2.Word.oddSteps
    exact List.length_take_of_le hkLen
  simpa [hOddTake] using hExp

/-- standard terminal contraction は encoded odd-only terminal contraction。 -/
theorem upperExponentWord_terminalContracting
    (F : FirstFailureEdge) :
    Collatz2.Word.Contracting F.upperExponentWord := by
  apply (Collatz2.Word.contracting_iff_threePow_lt_twoPow).2
  have h := F.upper_threePow_lt_modulus
  unfold AdjacentFerrersSwap.modulus at h
  simpa using h

/-- actual first-failure upper word は odd-only 側でも FirstCrossing。 -/
theorem upperExponentWord_firstCrossing
    (F : FirstFailureEdge) :
    Collatz2.Word.FirstCrossing F.upperExponentWord := {
  nonempty := F.upperExponentWord_nonempty
  properPositive := F.upperExponentWord_properPositive
  terminalNegative := F.upperExponentWord_terminalContracting
}

/-- terminal gap も standard/odd-only の二表現で一致する。 -/
theorem upperExponentWord_terminalGap
    (F : FirstFailureEdge) :
    Collatz2.Word.terminalGap F.upperExponentWord =
      wordTerminalGap F.step.edge.upperWord := by
  unfold Collatz2.Word.terminalGap wordTerminalGap
  rw [F.upperExponentWord_twoSteps, F.upperExponentWord_oddSteps]
  simp

/-! ## 3. normalized upper coordinate as a natural small residue -/

/-- nonnegative upper normalized defect の natural representative。 -/
def upperNormalizedDefectNat (F : FirstFailureEdge) : ℕ :=
  representativeAffineEndpoint F.step.edge.upperWord -
    leastRepresentative F.step.edge.upperWord

/-- upper failure では least representative は canonical affine endpoint 以下。 -/
theorem upperR_le_representativeAffineEndpoint
    (F : FirstFailureEdge) :
    leastRepresentative F.step.edge.upperWord ≤
      representativeAffineEndpoint F.step.edge.upperWord := by
  have h := F.upper_normalizedSeparationDefectInt_nonneg
  unfold normalizedSeparationDefectInt at h
  omega

/-- natural `q` を integer に戻すと既存 normalized defect と一致。 -/
theorem upperNormalizedDefectNat_cast
    (F : FirstFailureEdge) :
    (F.upperNormalizedDefectNat : ℤ) =
      normalizedSeparationDefectInt F.step.edge.upperWord := by
  unfold upperNormalizedDefectNat normalizedSeparationDefectInt
  rw [Nat.cast_sub F.upperR_le_representativeAffineEndpoint]

/-- natural upper coordinate は common odd count 未満。 -/
theorem upperNormalizedDefectNat_lt_oddTotal
    (F : FirstFailureEdge) :
    F.upperNormalizedDefectNat < F.step.edge.oddTotal := by
  have h := F.upper_normalizedSeparationDefectInt_lt_oddTotal
  rw [← F.upperNormalizedDefectNat_cast] at h
  exact_mod_cast h

/-- encoded word の odd step 数で書いた small strip。 -/
theorem upperNormalizedDefectNat_lt_oddSteps
    (F : FirstFailureEdge) :
    F.upperNormalizedDefectNat <
      Collatz2.Word.oddSteps F.upperExponentWord := by
  rw [F.upperExponentWord_oddSteps]
  exact F.upperNormalizedDefectNat_lt_oddTotal

/--
upper affine equation を natural small coordinate で書き直す。
-/
theorem upper_affineConst_eq_gap_mul_R_add_modulus_mul_upperQ
    (F : FirstFailureEdge) :
    affineConst F.step.edge.upperWord =
      wordTerminalGap F.step.edge.upperWord * F.step.edge.upperR +
        F.step.edge.modulus * F.upperNormalizedDefectNat := by
  have h :=
    FirstFailureFareyData.upper_affineConst_eq_gap_mul_R_add_modulus_mul_normalized
      (F := F)
  rw [← F.upperNormalizedDefectNat_cast] at h
  exact_mod_cast h

/-- odd-only representation へ移した同じ upper affine equation。 -/
theorem upperExponentWord_affineConst_eq_gap_mul_R_add_twoPow_mul_upperQ
    (F : FirstFailureEdge) :
    Collatz2.Word.affineConst F.upperExponentWord =
      Collatz2.Word.terminalGap F.upperExponentWord * F.step.edge.upperR +
        2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
          F.upperNormalizedDefectNat := by
  calc
    Collatz2.Word.affineConst F.upperExponentWord
        = affineConst F.step.edge.upperWord := F.upperExponentWord_affineConst
    _ =
      wordTerminalGap F.step.edge.upperWord * F.step.edge.upperR +
        F.step.edge.modulus * F.upperNormalizedDefectNat :=
          F.upper_affineConst_eq_gap_mul_R_add_modulus_mul_upperQ
    _ =
      Collatz2.Word.terminalGap F.upperExponentWord * F.step.edge.upperR +
        2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
          F.upperNormalizedDefectNat := by
            rw [F.upperExponentWord_terminalGap]
            unfold AdjacentFerrersSwap.modulus
            rw [F.upperExponentWord_twoSteps]

/-! ## 4. weighted-rank congruence -/

/-- mod terminal gap では `2^H = 3^p`。 -/
theorem upperExponentWord_twoPow_cast_eq_threePow_cast
    (F : FirstFailureEdge) :
    (((2 ^ Collatz2.Word.twoSteps F.upperExponentWord : ℕ)) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
      (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
  let w := F.upperExponentWord
  have hC := F.upperExponentWord_firstCrossing.terminalContracting
  have hPow :
      3 ^ Collatz2.Word.oddSteps w < 2 ^ Collatz2.Word.twoSteps w :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1 hC
  have hAdd :
      Collatz2.Word.terminalGap w + 3 ^ Collatz2.Word.oddSteps w =
        2 ^ Collatz2.Word.twoSteps w := by
    unfold Collatz2.Word.terminalGap
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  have hCast :=
    congrArg
      (fun n : ℕ => (n : ZMod (Collatz2.Word.terminalGap w)))
      hAdd
  have hGapZero :
      ((Collatz2.Word.terminalGap w : ℕ) :
        ZMod (Collatz2.Word.terminalGap w)) = 0 := by
    exact ZMod.natCast_self _
  simp only [Nat.cast_add] at hCast
  rw [hGapZero, zero_add] at hCast
  simpa [w] using hCast.symm

/--
normalized defect equation を mod G に落とすと

  B = 3^m * q  (mod G).
-/
theorem upperExponentWord_affineConst_cast_eq_threePow_mul_upperQ
    (F : FirstFailureEdge) :
    ((Collatz2.Word.affineConst F.upperExponentWord : ℕ) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
      (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        ((F.upperNormalizedDefectNat : ℕ) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
  have hNat :=
    F.upperExponentWord_affineConst_eq_gap_mul_R_add_twoPow_mul_upperQ
  have hCast :=
    congrArg
      (fun n : ℕ =>
        (n : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)))
      hNat
  simp only [Nat.cast_add, Nat.cast_mul] at hCast
  have hGapZero :
      ((Collatz2.Word.terminalGap F.upperExponentWord : ℕ) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) = 0 := by
    exact ZMod.natCast_self _
  rw [hGapZero, zero_mul, zero_add] at hCast
  rw [F.upperExponentWord_twoPow_cast_eq_threePow_cast] at hCast
  exact hCast

/--
既存 RankUnitData が使える endpoint では、actual first failure の small coordinate が
weighted rank sum そのものを決める。

  3*q = weightedRankSum  (mod G).
-/
theorem weightedRankSum_eq_three_mul_upperNormalizedDefectNat
    (F : FirstFailureEdge)
    (R : Collatz2.Word.RankUnitData F.upperExponentWord) :
    (((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
        ((F.upperNormalizedDefectNat : ℕ) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
      Collatz2.Word.weightedRankSum R := by
  have hB := F.upperExponentWord_affineConst_cast_eq_threePow_mul_upperQ
  have hW :=
    R.three_mul_affineConst_cast_eq_threePow_mul_weightedRankSum
      F.upperExponentWord_firstCrossing
  have hW' :
      (((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
          ((Collatz2.Word.affineConst F.upperExponentWord : ℕ) :
            ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
        (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
            ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
          Collatz2.Word.weightedRankSum R := by
    simpa only [Nat.cast_mul] using hW
  rw [hB] at hW'
  have hCancel :
      (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        ((((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
          ((F.upperNormalizedDefectNat : ℕ) :
            ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) =
      (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        Collatz2.Word.weightedRankSum R := by
    calc
      (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
            ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
          ((((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
            ((F.upperNormalizedDefectNat : ℕ) :
              ZMod (Collatz2.Word.terminalGap F.upperExponentWord)))
          =
        (((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
          ((((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
              ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
            ((F.upperNormalizedDefectNat : ℕ) :
              ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) := by
                ring
      _ =
        (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ)) :
            ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
          Collatz2.Word.weightedRankSum R := hW'
  exact R.cancel_threePow hCancel

/--
actual first failure の weighted-rank residue は、幅 `m` の ordinary set
`{3q | 0 ≤ q < m}` に必ず入る。

`q` は Nat なので `0 ≤ q` は型から自動。
-/
theorem weightedRank_small_residue_packet
    (F : FirstFailureEdge)
    (R : Collatz2.Word.RankUnitData F.upperExponentWord) :
    ∃ q : ℕ,
      q < Collatz2.Word.oddSteps F.upperExponentWord ∧
      (q : ℤ) = normalizedSeparationDefectInt F.step.edge.upperWord ∧
      (((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
          ((q : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
        Collatz2.Word.weightedRankSum R := by
  refine ⟨F.upperNormalizedDefectNat,
    F.upperNormalizedDefectNat_lt_oddSteps,
    F.upperNormalizedDefectNat_cast,
    F.weightedRankSum_eq_three_mul_upperNormalizedDefectNat R⟩

/--
primitive endpoint `gcd(k,m)=1` では既存 rank-unit theorem により、
small-residue weighted-rank packet は追加仮定なしで存在する。
-/
theorem exists_weightedRank_small_residue_packet_of_coprime
    (F : FirstFailureEdge)
    (hcop : Nat.Coprime F.step.edge.length F.step.edge.oddTotal) :
    ∃ R : Collatz2.Word.RankUnitData F.upperExponentWord,
      ∃ q : ℕ,
        q < Collatz2.Word.oddSteps F.upperExponentWord ∧
        (q : ℤ) = normalizedSeparationDefectInt F.step.edge.upperWord ∧
        (((3 : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord))) *
            ((q : ℕ) : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
          Collatz2.Word.weightedRankSum R := by
  have hcopWord :
      Nat.Coprime
        (Collatz2.Word.twoSteps F.upperExponentWord)
        (Collatz2.Word.oddSteps F.upperExponentWord) := by
    simpa using hcop
  obtain ⟨R⟩ :=
    F.upperExponentWord_firstCrossing.exists_rankUnitData_of_coprime hcopWord
  exact ⟨R, F.weightedRank_small_residue_packet R⟩

end FirstFailureEdge

end CSTMicro
end Collatz2
