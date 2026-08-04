import CollatzLean.CollatzSecondLayer.SynchronizationTransport

/-!
# long synchronizationの循環正規化

同期prefix `W` がsuffix `R` 内に収まる十分大きな項について
`R = W ++ V` を `Q = V ++ W` へ循環移動する。
prepared carryを、同期長0のexact difference / deferred carryへ正規化し、
多項式小性からcanonical boundaryとnegative predecessor shadowも保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord.Runs

/-- 連結語のrunを前半runと後半runへ分割する。 -/
theorem split_append
    {u v : ExpWord}
    {x z : ℕ}
    (h : Runs (u ++ v) x z) :
    ∃ y : ℕ, Runs u x y ∧ Runs v y z := by
  induction u generalizing x with
  | nil =>
      refine ⟨x, Runs.nil x, ?_⟩
      simpa using h
  | cons e u ih =>
      cases h with
      | cons he hstep hy htail =>
          obtain ⟨y, hu, hv⟩ := ih htail
          exact ⟨y, Runs.cons he hstep hy hu, hv⟩

/-- 前半runと後半runを連結する。 -/
theorem append
    {u v : ExpWord}
    {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z) :
    Runs (u ++ v) x z := by
  induction hu with
  | nil x =>
      simpa using hv
  | @cons e w x y t he hstep hy htail ih =>
      exact Runs.cons he hstep hy (ih hv)

/-- 正値から始まるrunの終点は、開始値の`2^length`倍以下。 -/
theorem end_le_twoPow_length_mul
    {w : ExpWord}
    {x y : ℕ}
    (h : Runs w x y)
    (hx : 0 < x) :
    y ≤ 2 ^ w.length * x := by
  induction h with
  | nil x =>
      simp
  | @cons e w x y z he hstep hy htail ih =>
      have hpow : 2 ≤ 2 ^ e := by
        cases e with
        | zero => omega
        | succ e =>
            rw [pow_succ]
            have hp : 0 < 2 ^ e := Nat.pow_pos (by omega)
            omega
      have hypos : 0 < y := by
        rcases hy with ⟨k, hk⟩
        omega
      have htwo : 2 * y ≤ 3 * x + 1 := by
        calc
          2 * y ≤ 2 ^ e * y :=
            Nat.mul_le_mul_right y hpow
          _ = 3 * x + 1 := hstep
      have hfour : 3 * x + 1 ≤ 4 * x := by omega
      have hybound : y ≤ 2 * x := by omega
      calc
        z ≤ 2 ^ w.length * y := ih hypos
        _ ≤ 2 ^ w.length * (2 * x) :=
          Nat.mul_le_mul_left _ hybound
        _ = 2 ^ (e :: w).length * x := by
          simp only [List.length_cons, pow_succ]
          ring

end ExpWord.Runs

/-- 同じ語・同じ開始値を持つ二つのアフィン実現の終点は一意。 -/
theorem realizes_end_unique
    {w : ExpWord}
    {x y z : ℕ}
    (hy : Realizes w x y)
    (hz : Realizes w x z) :
    y = z := by
  unfold Realizes at hy hz
  have hmul : 2 ^ twoSteps w * y = 2 ^ twoSteps w * z := by
    calc
      2 ^ twoSteps w * y
          = 3 ^ oddSteps w * x + affineConst w := hy
      _ = 2 ^ twoSteps w * z := hz.symm
  exact Nat.mul_left_cancel
    (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hmul

/-- `2^q ≤ 3^q`。 -/
lemma twoPow_le_threePow (q : ℕ) :
    2 ^ q ≤ 3 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul ih (by omega)

/--
一つのSpecial C3 chain項を循環移動するためのactual runデータ。
-/
structure RotationSourceData where
  R : ExpWord
  W : ExpWord
  V : ExpWord
  lowerStart : ℕ
  upperStart : ℕ
  rotatedStart : ℕ
  rotatedFinish : ℕ
  depth : ℕ
  differenceOddPart : ℕ
  lowerNextOddPart : ℕ
  suffix_eq : R = W ++ V
  R_nonempty : R ≠ []
  lowerPrefixRun : Runs W lowerStart rotatedStart
  remainingRun : Runs V rotatedStart upperStart
  upperPrefixRun : Runs W upperStart rotatedFinish
  difference :
    rotatedFinish = rotatedStart +
      2 ^ depth * differenceOddPart
  differenceOdd : Odd differenceOddPart
  lowerExact :
    ExactTwoFactor (3 * rotatedStart + 1)
      depth lowerNextOddPart
  upperCarry :
    ∃ quotient : ℕ,
      3 * rotatedFinish + 1 =
        2 ^ (depth + 1) * quotient

namespace RotationSourceData

/-- 循環移動語。 -/
def rotatedWord (D : RotationSourceData) : ExpWord :=
  D.V ++ D.W

/-- 循環移動語の長さは元suffix長と同じ。 -/
theorem rotatedWord_length (D : RotationSourceData) :
    D.rotatedWord.length = D.R.length := by
  rw [D.suffix_eq]
  simp [rotatedWord, Nat.add_comm]

/-- 循環移動語の総2除算数は元suffixと同じ。 -/
theorem rotatedWord_twoSteps (D : RotationSourceData) :
    twoSteps D.rotatedWord = twoSteps D.R := by
  rw [D.suffix_eq]
  simp [rotatedWord, twoSteps_append, Nat.add_comm]

/-- 循環移動後もactual run。 -/
theorem rotatedRun (D : RotationSourceData) :
    Runs D.rotatedWord D.rotatedStart D.rotatedFinish := by
  simpa [rotatedWord] using
    ExpWord.Runs.append D.remainingRun D.upperPrefixRun

/-- 循環移動後の開始値は終点より小さい。 -/
theorem rotatedStart_lt_finish (D : RotationSourceData) :
    D.rotatedStart < D.rotatedFinish := by
  rw [D.difference]
  apply Nat.lt_add_of_pos_right
  exact Nat.mul_pos
    (Nat.pow_pos (by omega))
    (by
      rcases D.differenceOdd with ⟨k, hk⟩
      omega)

/-- 循環移動語は非空。 -/
theorem rotatedWord_nonempty (D : RotationSourceData) :
    D.rotatedWord ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  have hRlen := congrArg List.length D.suffix_eq
  simp only [rotatedWord, List.length_append, List.length_nil, Nat.add_eq_zero_iff,
    List.length_eq_zero_iff] at hlen hRlen
  cases hR : D.R with
  | nil =>
      exact D.R_nonempty hR
  | cons e w =>
      rcases hlen with ⟨hV, hW⟩
      simp [hR, hV, hW] at hRlen

end RotationSourceData

/-- canonical・negative-shadowまで正規化された一項。 -/
structure RotationNormalizedData extends RotationSourceData where
  canonicalStart :
    rotatedStart =
      CollatzFirstLayer.ExpWord.canonicalStart
        (RotationSourceData.rotatedWord toRotationSourceData)
  canonicalFinish :
    rotatedFinish =
      canonicalEnd
        (RotationSourceData.rotatedWord toRotationSourceData)
  negativePredecessorShadow :
    predecessorShadow
        (RotationSourceData.rotatedWord toRotationSourceData) < 0

/--
循環移動後の開始値がcanonical modulus未満で、終点が`2*3^q`未満なら、
canonical boundaryとnegative predecessor shadowを得る。
-/
def rotationNormalize_of_small
    (D : RotationSourceData)
    (hstart : D.rotatedStart < residueModulus D.rotatedWord)
    (hfinish :
      (D.rotatedFinish : ℤ) <
        2 * (3 : ℤ) ^ oddSteps D.rotatedWord) :
    RotationNormalizedData := by
  have hendOdd : Odd D.rotatedFinish :=
    D.rotatedRun.end_odd_of_ne_nil D.rotatedWord_nonempty
  have hmod :=
    natural_start_mod_eq_canonicalStart
      D.rotatedRun.realizes hendOdd
  have hreduce :
      D.rotatedStart % residueModulus D.rotatedWord =
        D.rotatedStart :=
    Nat.mod_eq_of_lt hstart
  rw [hreduce] at hmod
  have hcanonicalRealizes :
      Realizes D.rotatedWord D.rotatedStart (canonicalEnd D.rotatedWord) := by
    have h := canonicalEnd_realizes D.rotatedWord
    rw [← hmod] at h
    exact h
  have hend : D.rotatedFinish = canonicalEnd D.rotatedWord :=
    realizes_end_unique D.rotatedRun.realizes hcanonicalRealizes
  exact
    { toRotationSourceData := D
      canonicalStart := hmod
      canonicalFinish := hend
      negativePredecessorShadow := by
        rw [predecessorShadow_neg_iff, ← hend]
        exact hfinish }

/-
chain Special C3項の循環移動に使う語と、
その語に関する基本的な分解補題。
-/
namespace ChainSpecialRotation

/-- 同期prefixとして使う境界語。 -/
noncomputable def prefixWord
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    ExpWord :=
  (chainAnalysisPacket C n).prepared.boundary.word

/-- 同期prefixの長さ。 -/
noncomputable def prefixLength
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    ℕ :=
  (prefixWord C n).length

/-- suffixから同期prefixを除いた残りの語。 -/
noncomputable def remainingWord
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    ExpWord :=
  (C.pair n).R.drop (prefixLength C n)

/--
境界長は同期prefix語の長さに一致する。
-/
theorem boundary_length_eq_prefixLength
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    (chainAnalysisPacket C n).prepared.boundary.length =
      prefixLength C n := by
  have hlen :=
    congrArg List.length
      (chainAnalysisPacket C n).prepared.boundary.word_eq
  simpa [prefixLength, prefixWord] using hlen.symm

/--
同期prefix語は、下側endpointから始まる実軌道segmentである。
-/
theorem prefixWord_eq_segmentWord
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    prefixWord C n =
      O.segmentWord
        (C.endpointPosition n)
        (prefixLength C n) := by
  calc
    prefixWord C n =
        O.segmentWord
          (chainAnalysisPacket C n).prepared.lowerOrbit.index
          (chainAnalysisPacket C n).prepared.boundary.length := by
      simpa [prefixWord] using
        (chainAnalysisPacket C n).prepared.boundary.word_eq
    _ =
        O.segmentWord
          (C.endpointPosition n)
          (prefixLength C n) := by
      rw [boundary_length_eq_prefixLength C n]
      rfl

/--
同期prefixがsuffix内に収まるなら、
suffixの先頭部分は同期prefix語そのものである。
-/
theorem take_eq_prefixWord
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ)
    (hsync :
      prefixLength C n ≤
        (C.pair n).R.length) :
    (C.pair n).R.take (prefixLength C n) =
      prefixWord C n := by
  have hrunOrbit :
      Runs (C.pair n).R
        (O.value (C.endpointPosition n))
        (C.pair n).YAR := by
    rw [C.lowerEndpointValue n]
    exact (C.pair n).runR
  have hR :
      (C.pair n).R =
        O.segmentWord
          (C.endpointPosition n)
          (C.pair n).R.length := by
    exact
      (ExpWord.Runs.eq_segment_of_orbit_start hrunOrbit).1
  calc
    List.take (prefixLength C n) (C.pair n).R =
        List.take
          (prefixLength C n)
          (O.segmentWord
            (C.endpointPosition n)
            (C.pair n).R.length) := by
      exact congrArg (List.take (prefixLength C n)) hR
    _ =
        O.segmentWord
          (C.endpointPosition n)
          (prefixLength C n) :=
      O.segmentWord_take_of_le hsync
    _ = prefixWord C n :=
      (prefixWord_eq_segmentWord C n).symm

/--
元suffixは、同期prefixと残りの語へ分解される。
-/
theorem suffix_eq
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ)
    (hsync :
      prefixLength C n ≤
        (C.pair n).R.length) :
    (C.pair n).R =
      prefixWord C n ++ remainingWord C n := by
  calc
    (C.pair n).R =
        (C.pair n).R.take (prefixLength C n) ++
          (C.pair n).R.drop (prefixLength C n) :=
      (List.take_append_drop
        (prefixLength C n)
        (C.pair n).R).symm
    _ = prefixWord C n ++ remainingWord C n := by
      rw [take_eq_prefixWord C n hsync]
      rfl

/--
同期prefixの下側actual run。
-/
theorem lowerPrefixRun
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    Runs (prefixWord C n)
      (C.pair n).YA
      (chainAnalysisPacket C n).prepared.boundary.lowerFinish := by
  change
    Runs
      (chainAnalysisPacket C n).prepared.boundary.word
      (chainAnalysisPacket C n).criticalPair.YA
      (chainAnalysisPacket C n).prepared.boundary.lowerFinish
  exact
    (chainAnalysisPacket C n).prepared.boundary.lowerRun

/--
同期prefixの上側actual run。
-/
theorem upperPrefixRun
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    Runs (prefixWord C n)
      (C.pair n).YAR
      (chainAnalysisPacket C n).prepared.upperFinish := by
  change
    Runs
      (chainAnalysisPacket C n).prepared.boundary.word
      (chainAnalysisPacket C n).criticalPair.YAR
      (chainAnalysisPacket C n).prepared.upperFinish
  exact
    (chainAnalysisPacket C n).prepared.upperRun
/--
元suffixのrunを同期prefixと残りのrunへ分割する。
-/
theorem remainingRun
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ)
    (hsync :
      prefixLength C n ≤
        (C.pair n).R.length) :
    Runs (remainingWord C n)
      (chainAnalysisPacket C n).prepared.boundary.lowerFinish
      (C.pair n).YAR := by
  have hrunSplit :
      Runs
        (prefixWord C n ++ remainingWord C n)
        (C.pair n).YA
        (C.pair n).YAR := by
    rw [← suffix_eq C n hsync]
    exact (C.pair n).runR
  obtain ⟨middle, hPrefixRun, hRemainingRun⟩ :=
    ExpWord.Runs.split_append hrunSplit
  have hmiddle :
      middle =
        (chainAnalysisPacket C n).prepared.boundary.lowerFinish :=
    hPrefixRun.end_unique (lowerPrefixRun C n)
  subst middle
  exact hRemainingRun

/--
循環移動後の上下差を、carry depthと奇数部分へ分解する。
-/
theorem rotatedDifference
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    (chainAnalysisPacket C n).prepared.upperFinish =
      (chainAnalysisPacket C n).prepared.boundary.lowerFinish +
        2 ^ (chainAnalysisPacket C n).carry.d *
          (3 ^ oddSteps (prefixWord C n) *
            (chainAnalysisPacket C n).prepared.ordered.oddPart) := by
  simpa [prefixWord,
    ChainAnalysisPacket.carry,
    PreparedCarryData.toCarryComparison,
    PreparedCarryData.remainingDepth,
    Nat.mul_assoc] using
    (chainAnalysisPacket C n).prepared.upperDifference

/--
deferred carryのdepthは、下側境界の次の2除算指数に一致する。
-/
theorem carryDepth_eq_nextExponent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (H : ChainSpecialC3At (chainAnalysisPacket C n)) :
    (chainAnalysisPacket C n).carry.d =
      (chainAnalysisPacket C n).prepared.boundary.nextExponent := by
  have h := H.deferredCarry.depth_eq
  simpa [ChainAnalysisPacket.carry,
    PreparedCarryData.toCarryComparison] using h

/--
循環移動後の開始値についてのexact two-factor分解。
-/
theorem lowerExact
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (H : ChainSpecialC3At (chainAnalysisPacket C n)) :
    ExactTwoFactor
      (3 *
          (chainAnalysisPacket C n).prepared.boundary.lowerFinish +
        1)
      (chainAnalysisPacket C n).carry.d
      (chainAnalysisPacket C n).prepared.boundary.nextOddPart := by
  refine
    ⟨?_,
      (chainAnalysisPacket C n).prepared.boundary.lowerNextOdd⟩
  rw [carryDepth_eq_nextExponent H]
  exact
    (chainAnalysisPacket C n).prepared.boundary.lowerNextFactorization

end ChainSpecialRotation

/--
chain Special C3項で、同期prefixがsuffix内に収まる場合の
rotation source。
-/
noncomputable def rotationSourceOfChainSpecial
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (H : ChainSpecialC3At (chainAnalysisPacket C n))
    (hsync :
      (chainAnalysisPacket C n).prepared.boundary.word.length ≤
        (C.pair n).R.length) :
    RotationSourceData := by
  have hsync' :
      ChainSpecialRotation.prefixLength C n ≤
        (C.pair n).R.length := by
    simpa [ChainSpecialRotation.prefixLength,
      ChainSpecialRotation.prefixWord] using hsync
  exact
    { R := (C.pair n).R
      W := ChainSpecialRotation.prefixWord C n
      V := ChainSpecialRotation.remainingWord C n

      lowerStart := (C.pair n).YA
      upperStart := (C.pair n).YAR

      rotatedStart :=
        (chainAnalysisPacket C n).prepared.boundary.lowerFinish
      rotatedFinish :=
        (chainAnalysisPacket C n).prepared.upperFinish

      depth :=
        (chainAnalysisPacket C n).carry.d

      differenceOddPart :=
        3 ^ oddSteps (ChainSpecialRotation.prefixWord C n) *
          (chainAnalysisPacket C n).prepared.ordered.oddPart

      lowerNextOddPart :=
        (chainAnalysisPacket C n).prepared.boundary.nextOddPart

      suffix_eq :=
        ChainSpecialRotation.suffix_eq C n hsync'

      R_nonempty :=
        (C.pair n).R_nonempty

      lowerPrefixRun :=
        ChainSpecialRotation.lowerPrefixRun C n

      remainingRun :=
        ChainSpecialRotation.remainingRun C n hsync'

      upperPrefixRun :=
        ChainSpecialRotation.upperPrefixRun C n

      difference :=
        ChainSpecialRotation.rotatedDifference C n

      differenceOdd := by
        simpa [ChainSpecialRotation.prefixWord] using
          (chainAnalysisPacket C n).prepared.upperDifferenceOdd

      lowerExact :=
        ChainSpecialRotation.lowerExact H

      upperCarry :=
        ⟨H.deferredCarry.quotient,
          H.deferredCarry.extraFactor⟩ }

/-- chainのsuffix長は無限大へ進む。 -/
theorem orderedChain_suffixLengths_tend_to_infinity
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      M < (C.pair n).R.length := by
  intro M
  obtain ⟨J, hJ⟩ :=
    S.toC3CylinderSequence.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro n hn
  have hsource : J ≤ C.sourceIndex (n + 1) := by
    have hindex : n + 1 ≤ C.sourceIndex (n + 1) :=
      CoherentC3CylinderSequence.strictMono_nat_id_le
        C.sourceIndex C.sourceIndex_strict (n + 1)
    omega
  have htarget := hJ (C.sourceIndex (n + 1)) hsource
  exact lt_of_lt_of_le htarget (C.targetCylinderInside n)

/--
十分長いsuffixでは同期prefixがsuffix内に収まる。
-/
theorem rotationEligible_of_suffixLength_ge
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n N : ℕ}
    (hPow :
      ∀ q : ℕ, N ≤ q →
        C.endpointPolynomialK * (q + 1) ^ C.endpointPolynomialA <
          2 ^ (q + 1))
    (hLength : N ≤ (C.pair n).R.length) :
    (chainAnalysisPacket C n).prepared.boundary.word.length ≤
      (C.pair n).R.length := by
  let P := chainAnalysisPacket C n
  let r := P.prepared.boundary.word.length
  let q := (C.pair n).R.length
  have hrDepth : r ≤ P.ordered.depth := by
    have hvalid := P.prepared.boundary.lowerRun.valid
    have hrTwo : r ≤ twoSteps P.prepared.boundary.word := by
      simpa [r, oddSteps] using oddSteps_le_twoSteps hvalid
    have htwoDepth :
        twoSteps P.prepared.boundary.word ≤ P.ordered.depth :=
      Nat.le_of_lt P.prepared.boundary.consumed_lt
    exact hrTwo.trans htwoDepth
  have hpowMono : 2 ^ r ≤ 2 ^ P.ordered.depth :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hrDepth
  have hdiff := P.ordered.twoPow_le_difference
  have hYApos : 0 < (C.pair n).YA := by
    rcases (C.pair n).runA.end_odd_of_ne_nil
      (C.pair n).A_nonempty with ⟨k, hk⟩
    omega
  have hYALe : (C.pair n).YA ≤ (C.pair n).YAR :=
    Nat.le_of_lt P.ordered.value_lt
  have hdiffLt :
      (C.pair n).YAR - (C.pair n).YA < (C.pair n).YAR :=
    Nat.sub_lt_self hYApos hYALe
  have hpoly := C.endpointPolynomial n
  have hpowPoly : 2 ^ r ≤
      C.endpointPolynomialK * (q + 1) ^ C.endpointPolynomialA :=
    hpowMono.trans
      (hdiff.trans ((Nat.le_of_lt hdiffLt).trans hpoly))
  have hpolyPow := hPow q (by simpa [q] using hLength)
  have hpowLt : 2 ^ r < 2 ^ (q + 1) :=
    lt_of_le_of_lt hpowPoly hpolyPow
  have hrLt : r < q + 1 := by
    by_contra hnot
    have hexp : q + 1 ≤ r := Nat.le_of_not_gt hnot
    have hmono : 2 ^ (q + 1) ≤ 2 ^ r :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hexp
    omega
  simpa [r, q] using Nat.le_of_lt_succ hrLt

namespace ChainSpecialRotation

/--
同期prefix語の長さに対応する2冪は、
上側endpointの多項式上界以下である。
-/
theorem prefixTwoPow_le_endpointPolynomial
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    2 ^ (prefixWord C n).length ≤
      C.endpointPolynomialK *
        ((C.pair n).R.length + 1) ^ C.endpointPolynomialA := by
  let P := chainAnalysisPacket C n
  let r := P.prepared.boundary.word.length
  let q := (C.pair n).R.length
  have hrDepth :
      r ≤ P.ordered.depth := by
    have hvalid :=
      P.prepared.boundary.lowerRun.valid
    have hrTwo :
        r ≤ twoSteps P.prepared.boundary.word := by
      simpa [r, oddSteps] using
        oddSteps_le_twoSteps hvalid
    exact
      hrTwo.trans
        (Nat.le_of_lt P.prepared.boundary.consumed_lt)
  have hpowMono :
      2 ^ r ≤ 2 ^ P.ordered.depth :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      hrDepth
  have hdiff :=
    P.ordered.twoPow_le_difference
  have hYApos :
      0 < (C.pair n).YA := by
    rcases
        (C.pair n).runA.end_odd_of_ne_nil
          (C.pair n).A_nonempty with
      ⟨k, hk⟩
    omega
  have hYALe :
      (C.pair n).YA ≤ (C.pair n).YAR :=
    Nat.le_of_lt P.ordered.value_lt
  have hdiffLt :
      (C.pair n).YAR - (C.pair n).YA <
        (C.pair n).YAR :=
    Nat.sub_lt_self hYApos hYALe
  have hpoly :=
    C.endpointPolynomial n
  have hchain :
      2 ^ r ≤
        C.endpointPolynomialK *
          (q + 1) ^ C.endpointPolynomialA := by
    exact
      hpowMono.trans
        ((hdiff.trans (Nat.le_of_lt hdiffLt)).trans hpoly)
  simpa [P, r, q, prefixWord] using hchain

/--
chain pairの上側endpointは正である。
-/
theorem upperEndpoint_pos
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) :
    0 < (C.pair n).YAR := by
  rcases
      (C.pair n).runR.end_odd_of_ne_nil
        (C.pair n).R_nonempty with
    ⟨k, hk⟩
  omega

/--
循環移動後の終点は、endpoint多項式上界の平方以下である。
-/
theorem rotationSource_finish_le_polynomialSquare
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (H : ChainSpecialC3At (chainAnalysisPacket C n))
    (hsync :
      (chainAnalysisPacket C n).prepared.boundary.word.length ≤
        (C.pair n).R.length) :
    (rotationSourceOfChainSpecial H hsync).rotatedFinish ≤
      (C.endpointPolynomialK * C.endpointPolynomialK) *
        ((C.pair n).R.length + 1) ^
          (C.endpointPolynomialA + C.endpointPolynomialA) := by
  let D :=
    rotationSourceOfChainSpecial H hsync
  have hpowW :
      2 ^ D.W.length ≤
        C.endpointPolynomialK *
          ((C.pair n).R.length + 1) ^
            C.endpointPolynomialA := by
    change
      2 ^ (prefixWord C n).length ≤
        C.endpointPolynomialK *
          ((C.pair n).R.length + 1) ^
            C.endpointPolynomialA
    exact prefixTwoPow_le_endpointPolynomial C n
  have hupper :
      D.upperStart ≤
        C.endpointPolynomialK *
          ((C.pair n).R.length + 1) ^
            C.endpointPolynomialA := by
    change
      (C.pair n).YAR ≤
        C.endpointPolynomialK *
          ((C.pair n).R.length + 1) ^
            C.endpointPolynomialA
    exact C.endpointPolynomial n
  have hupperPos :
      0 < D.upperStart := by
    change 0 < (C.pair n).YAR
    exact upperEndpoint_pos C n
  have hgrowth :
      D.rotatedFinish ≤
        2 ^ D.W.length * D.upperStart :=
    ExpWord.Runs.end_le_twoPow_length_mul
      D.upperPrefixRun
      hupperPos
  change
    D.rotatedFinish ≤
      (C.endpointPolynomialK * C.endpointPolynomialK) *
        ((C.pair n).R.length + 1) ^
          (C.endpointPolynomialA + C.endpointPolynomialA)
  calc
    D.rotatedFinish
        ≤ 2 ^ D.W.length * D.upperStart :=
      hgrowth
    _ ≤
        (C.endpointPolynomialK *
            ((C.pair n).R.length + 1) ^
              C.endpointPolynomialA) *
          (C.endpointPolynomialK *
            ((C.pair n).R.length + 1) ^
              C.endpointPolynomialA) :=
      Nat.mul_le_mul hpowW hupper
    _ =
        (C.endpointPolynomialK * C.endpointPolynomialK) *
          ((C.pair n).R.length + 1) ^
            (C.endpointPolynomialA +
              C.endpointPolynomialA) := by
      rw [pow_add]
      ring

end ChainSpecialRotation

namespace RotationSourceData

/--
元suffix長に対応する`2^(q+1)`は、
循環移動語のcanonical modulus以下である。
-/
theorem twoPow_succ_length_le_residueModulus
    (D : RotationSourceData) :
    2 ^ (D.R.length + 1) ≤
      residueModulus D.rotatedWord := by
  have hlengthTwoSteps :
      D.R.length ≤ twoSteps D.rotatedWord := by
    have hvalid :=
      D.rotatedRun.valid
    have hlen :=
      oddSteps_le_twoSteps hvalid
    simpa [oddSteps, D.rotatedWord_length] using hlen
  unfold residueModulus
  exact
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (by omega)

/--
循環移動後の終点が`2^(q+1)`未満なら、
循環移動後の開始値はcanonical modulus未満である。
-/
theorem rotatedStart_lt_residueModulus_of_finish_lt
    (D : RotationSourceData)
    (hfinish :
      D.rotatedFinish < 2 ^ (D.R.length + 1)) :
    D.rotatedStart <
      residueModulus D.rotatedWord := by
  exact
    lt_of_lt_of_le
      (lt_trans D.rotatedStart_lt_finish hfinish)
      D.twoPow_succ_length_le_residueModulus

/--
`2^(q+1)`未満という終点評価から、
negative predecessor shadowに必要な整数上界を得る。
-/
theorem rotatedFinish_int_lt_shadowBound_of_finish_lt
    (D : RotationSourceData)
    (hfinish :
      D.rotatedFinish < 2 ^ (D.R.length + 1)) :
    (D.rotatedFinish : ℤ) <
      2 * (3 : ℤ) ^ oddSteps D.rotatedWord := by
  have htwoThree :
      2 ^ (D.R.length + 1) ≤
        2 * 3 ^ D.R.length := by
    simpa [pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul_left 2
        (twoPow_le_threePow D.R.length)
  have hshadowNat :
      D.rotatedFinish <
        2 * 3 ^ D.R.length :=
    lt_of_lt_of_le hfinish htwoThree
  have hlength :
      oddSteps D.rotatedWord = D.R.length := by
    simpa [oddSteps] using D.rotatedWord_length
  rw [hlength]
  exact_mod_cast hshadowNat

/--
循環移動後の終点が`2^(q+1)`未満なら、
canonical・negative-shadow正規化を一度に得る。
-/
def normalize_of_finish_lt_twoPow_succ_length
    (D : RotationSourceData)
    (hfinish :
      D.rotatedFinish < 2 ^ (D.R.length + 1)) :
    RotationNormalizedData :=
  rotationNormalize_of_small D
    (D.rotatedStart_lt_residueModulus_of_finish_lt hfinish)
    (D.rotatedFinish_int_lt_shadowBound_of_finish_lt hfinish)

end RotationSourceData

/--
十分長いSpecial C3 chain項を、
canonical negative-shadow rotationへ正規化する。
-/
noncomputable def rotationNormalized_of_suffixLength_ge
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (H : ChainSpecialC3At (chainAnalysisPacket C n))
    {N₁ N₂ : ℕ}
    (hN₁ :
      ∀ q : ℕ, N₁ ≤ q →
        C.endpointPolynomialK *
            (q + 1) ^ C.endpointPolynomialA <
          2 ^ (q + 1))
    (hN₂ :
      ∀ q : ℕ, N₂ ≤ q →
        (C.endpointPolynomialK *
            C.endpointPolynomialK) *
            (q + 1) ^
              (C.endpointPolynomialA +
                C.endpointPolynomialA) <
          2 ^ (q + 1))
    (hLength :
      max N₁ N₂ ≤ (C.pair n).R.length) :
    RotationNormalizedData := by
  let q := (C.pair n).R.length
  have hq₁ :
      N₁ ≤ q := by
    dsimp [q]
    omega
  have hq₂ :
      N₂ ≤ q := by
    dsimp [q]
    omega
  have heligible :
      (chainAnalysisPacket C n).prepared.boundary.word.length ≤
        (C.pair n).R.length :=
    rotationEligible_of_suffixLength_ge hN₁ hq₁
  let D :=
    rotationSourceOfChainSpecial H heligible
  have hfinishPolynomial :
      D.rotatedFinish ≤
        (C.endpointPolynomialK *
            C.endpointPolynomialK) *
          (q + 1) ^
            (C.endpointPolynomialA +
              C.endpointPolynomialA) := by
    change
      (rotationSourceOfChainSpecial H heligible).rotatedFinish ≤
        (C.endpointPolynomialK *
            C.endpointPolynomialK) *
          ((C.pair n).R.length + 1) ^
            (C.endpointPolynomialA +
              C.endpointPolynomialA)
    exact
      ChainSpecialRotation.rotationSource_finish_le_polynomialSquare
          H heligible
  have hfinishSmall :
      D.rotatedFinish <
        2 ^ (D.R.length + 1) := by
    have hsmall :
        D.rotatedFinish < 2 ^ (q + 1) :=
      lt_of_le_of_lt
        hfinishPolynomial
        (hN₂ q hq₂)
    simpa [D, q, rotationSourceOfChainSpecial] using hsmall
  exact
    D.normalize_of_finish_lt_twoPow_succ_length hfinishSmall

/-- bounded-depth long-sync chainと、その十分後のrotation正規化。 -/
structure BoundedDepthLongSyncRotationData
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) where
  synchronizationLaw : ChainSynchronizationLaw C
  depthBound : ℕ
  depth_bounded : ∀ n : ℕ,
    synchronizationLaw.specialTail.start ≤ n →
    (chainAnalysisPacket C n).carry.d ≤ depthBound
  syncLength_tendsto :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      M <
        (chainAnalysisPacket C
          (synchronizationLaw.specialTail.start + n)).prepared.boundary.word.length
  rotationStart : ℕ
  rotated : ∀ n : ℕ, rotationStart ≤ n →
    RotationNormalizedData

/-- ある位置以後の全Special C3項がrotation正規化されること。 -/
structure EventuallyChainRotationData
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) where
  start : ℕ
  rotated : ∀ n : ℕ, start ≤ n → RotationNormalizedData

/--
最終的にSpecial C3であるchainは、十分後では各項をrotation正規化できる。
-/
theorem eventually_rotation_normalized
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (hPow : PolynomialBelowTwoPower)
    (E : EventuallyChainSpecialData C) :
    Nonempty (EventuallyChainRotationData C) := by
  obtain ⟨N₁, hN₁⟩ :=
    hPow C.endpointPolynomialK C.endpointPolynomialA
  obtain ⟨N₂, hN₂⟩ :=
    hPow
      (C.endpointPolynomialK * C.endpointPolynomialK)
      (C.endpointPolynomialA + C.endpointPolynomialA)
  obtain ⟨N₃, hN₃⟩ :=
    orderedChain_suffixLengths_tend_to_infinity C (max N₁ N₂)
  let N := max E.start N₃
  refine ⟨{
    start := N
    rotated := ?_
  }⟩
  intro n hn
  have hnSpecial : E.start ≤ n := by
    dsimp [N] at hn
    omega
  have hnLength : N₃ ≤ n := by
    dsimp [N] at hn
    omega
  have hlength : max N₁ N₂ ≤ (C.pair n).R.length :=
    Nat.le_of_lt (hN₃ n hnLength)
  exact rotationNormalized_of_suffixLength_ge
    (E.special n hnSpecial)
    hN₁ hN₂ hlength

/--
bounded-depth long-sync lawから、十分後のrotation正規化を含む残余データを構成する。
-/
noncomputable def boundedDepthLongSyncRotationData_of_law
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (hPow : PolynomialBelowTwoPower)
    (L : ChainSynchronizationLaw C)
    (B : ℕ)
    (hdepth : ∀ n : ℕ,
      L.specialTail.start ≤ n →
      (chainAnalysisPacket C n).carry.d ≤ B) :
    BoundedDepthLongSyncRotationData C := by
  let E := Classical.choice
    (eventually_rotation_normalized hPow L.specialTail)
  exact
    { synchronizationLaw := L
      depthBound := B
      depth_bounded := hdepth
      syncLength_tendsto :=
        L.syncLength_tendsto_of_depth_bounded B hdepth
      rotationStart := E.start
      rotated := E.rotated }

end CollatzSecondLayer
