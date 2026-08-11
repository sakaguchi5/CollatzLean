import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.NaturalZeroReplay
import CollatzLean.Collatz.Word.SharpAffine
import CollatzLean.Collatz.Word.SuffixGapBudget
import CollatzLean.Collatz.Word.AffineDecoder

/-!
# natural j=0 sign-change packet の有限語算術

first overshoot から自然発生する `j=0` packet を、
有限語 `v` と二つの局所 half-gap `n,d` の exact 算術へ圧縮する。

`w = 1 :: v` とし

* `S = canonicalStart w`
* `s = canonicalStart v`
* `t = canonicalEnd v = canonicalEnd w`

と置く。natural sign-change では `S < t < s` であり、

* `t = S + 2*n`
* `s = t + 2*d`

と書ける。`j=0` の head equation `2*s = 3*S+1` により

* `S + 1 = 4*(n+d)`
* `s + 1 = 6*(n+d)`
* `t + 1 = 6*n + 4*d`

が exact に成立する。

さらに tail の affine data を

* `A = 2^J`
* `C = 3^m`
* `B = affineConst v`
* `g = A-C`
* `G = 2*A-3*C`

と置くと、natural packet では

* `B + g = 6*n*g + 2*d*G`
* `3*B + A = G*s + 6*n*A`

が成立する。
`AllSuffixesContracting` の exact gap budget と合わせると

  `(m+1)A = G*s + 6*n*A + suffixGapBudget v`

を得る。特に `6*n <= m`。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData

/-- all-suffix-contracting は append の右側へそのまま降りる。 -/
private theorem allSuffixesContracting_append_right
    {u v : Collatz.Word}
    (h : Word.AllSuffixesContracting (u ++ v)) :
    Word.AllSuffixesContracting v := by
  induction u with
  | nil => simpa using h
  | cons e u ih =>
      change
        Word.Contracting (e :: (u ++ v)) ∧
          Word.AllSuffixesContracting (u ++ v) at h
      exact ih h.2

/-- first crossing の任意 cut 後 suffix は all-suffix-contracting。 -/
theorem suffixWord_allSuffixesContracting
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) {k : ℕ}
    (hk : k ≤ F.length) :
    Word.AllSuffixesContracting (suffixWord F k) := by
  have hAll := F.crossing.allSuffixesContracting
  have hdecomp :
      R.word.take F.length =
        O.segment R.startIndex k ++ suffixWord F k := by
    rw [F.word_eq_segment]
    unfold suffixWord
    calc
      O.segment R.startIndex F.length =
          O.segment R.startIndex (k + (F.length - k)) := by
            congr 2
            omega
      _ =
          O.segment R.startIndex k ++
            O.segment (R.startIndex + k) (F.length - k) :=
        O.segment_add R.startIndex k (F.length - k)
  rw [hdecomp] at hAll
  exact allSuffixesContracting_append_right hAll

/-- first-crossing endpoint は3で割れない。 -/
theorem endpoint_mod_three_ne_zero
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    F.endpointValue % 3 ≠ 0 := by
  intro hmod
  have hp : 0 < F.length := F.length_pos
  let k := F.length - 1
  have hk : k + 1 = F.length := by
    dsimp [k]
    omega
  have hstep :
      2 ^ O.exponent (R.startIndex + k) * F.endpointValue =
        3 * O.value (R.startIndex + k) + 1 := by
    unfold FirstCrossingData.endpointValue
    have h := O.step (R.startIndex + k)
    have hend :
        R.startIndex + F.length = (R.startIndex + k) + 1 := by
      rw [← hk]
      omega
    rw [hend]
    simpa using h
  have hdiv : 3 ∣ F.endpointValue := Nat.dvd_of_mod_eq_zero hmod
  rcases hdiv with ⟨q, hq⟩
  rw [hq] at hstep
  have hmodEq := congrArg (fun z : ℕ => z % 3) hstep
  norm_num [Nat.add_mod, Nat.mul_mod] at hmodEq

end FirstCrossingData

namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- cut 後 tail の短い名前。 -/
def tailWord
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : Collatz.Word :=
  suffixWord F D.cut

/-- predecessor suffix の短い名前。 -/
def predecessorWord
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : Collatz.Word :=
  suffixWord F D.pred

/-- tail length。 -/
def tailLength
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  Word.oddSteps D.tailWord

/-- tail total exponent。 -/
def tailExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  Word.twoSteps D.tailWord

/-- tail affine constant。 -/
def tailAffine
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  Word.affineConst D.tailWord

/-- tail `v` 自身の contracting gap `2^J-3^m`。 -/
def tailGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  2 ^ D.tailExponent - 3 ^ D.tailLength

/-- prepend-one word `1::v` の contracting gap `2^(J+1)-3^(m+1)`。 -/
def prependGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  2 ^ Word.twoSteps (1 :: D.tailWord) -
    3 ^ Word.oddSteps (1 :: D.tailWord)

/-- cut 後 tail は実際には strict descent。 -/
theorem tail_strict_descent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.canonicalEnd D.tailWord < Word.canonicalStart D.tailWord := by
  have hle :
      Word.canonicalEnd D.tailWord ≤ Word.canonicalStart D.tailWord := by
    simpa [tailWord] using D.tail_nonpositive
  have hne :
      Word.canonicalEnd D.tailWord ≠ Word.canonicalStart D.tailWord := by
    intro heq
    have hvalue :
        boundaryValue F D.cut = F.endpointValue := by
      rw [D.cutStart_eq, D.cutEnd_eq]
      simpa [tailWord] using heq.symm
    have hindex :=
      (O.value_injective_of_unbounded R.unbounded) hvalue
    have hcut : D.cut = F.length := by
      exact Nat.add_left_cancel hindex
    exact (Nat.ne_of_lt D.cut_lt) hcut
  omega

/-- cut 後 tail は actual segment 由来なので valid。 -/
theorem tail_valid
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Valid D.tailWord := by
  simpa [tailWord, suffixWord] using
    (O.runsSegment (R.startIndex + D.cut) (F.length - D.cut)).valid

/-- tail は all-suffix-contracting。 -/
theorem tail_allSuffixesContracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.AllSuffixesContracting D.tailWord := by
  simpa [tailWord] using
    FirstCrossingData.suffixWord_allSuffixesContracting
      F (Nat.le_of_lt D.cut_lt)

/-- predecessor suffix も all-suffix-contracting。 -/
theorem predecessor_allSuffixesContracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.AllSuffixesContracting D.predecessorWord := by
  have hpredLt : D.pred < F.length := by
    have hsucc := D.pred_succ
    have hcut := D.cut_lt
    omega
  simpa [predecessorWord] using
    FirstCrossingData.suffixWord_allSuffixesContracting
      F (Nat.le_of_lt hpredLt)

/-- tail 自身は contracting。 -/
theorem tail_contracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Contracting D.tailWord :=
  Word.AllSuffixesContracting.whole
    D.tail_nonempty D.tail_allSuffixesContracting

/-- predecessor `1::v` も contracting。 -/
theorem predecessor_contracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Contracting D.predecessorWord := by
  have hne : D.predecessorWord ≠ [] := by
    rw [predecessorWord, D.suffix_eq]
    simp
  exact Word.AllSuffixesContracting.whole
    hne D.predecessor_allSuffixesContracting

/-- prepend-one word `1::v` は contracting。 -/
theorem prepend_contracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Contracting (1 :: D.tailWord) := by
  have h := D.predecessor_contracting
  rw [predecessorWord, D.suffix_eq] at h
  simpa [tailWord] using h

/-- tail gap は正。 -/
theorem tailGap_pos
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    0 < D.tailGap := by
  exact Nat.sub_pos_of_lt (by
    simpa [tailGap, tailExponent, tailLength, Word.Contracting] using
      D.tail_contracting)

/-- prepend gap は正。 -/
theorem prependGap_pos
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    0 < D.prependGap := by
  exact Nat.sub_pos_of_lt (by
    simpa [prependGap, Word.Contracting] using D.prepend_contracting)

/-- `3*tailGap = 2^J + prependGap`。 -/
theorem three_mul_tailGap_eq_twoPow_add_prependGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    3 * D.tailGap = 2 ^ D.tailExponent + D.prependGap := by
  have htail :
      3 ^ D.tailLength + D.tailGap = 2 ^ D.tailExponent := by
    unfold tailGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [tailExponent, tailLength, Word.Contracting] using
        D.tail_contracting))
  have hprepend0 :
      3 ^ Word.oddSteps (1 :: D.tailWord) + D.prependGap =
        2 ^ Word.twoSteps (1 :: D.tailWord) := by
    unfold prependGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [Word.Contracting] using D.prepend_contracting))
  have hprepend' :
      3 ^ D.tailLength * 3 + D.prependGap =
        2 * (2 ^ D.tailExponent) := by
    simpa [tailLength, tailExponent,
      Word.oddSteps_cons, Word.twoSteps_cons, pow_add]
      using hprepend0
  have hprepend :
      3 * (3 ^ D.tailLength) + D.prependGap =
        2 * (2 ^ D.tailExponent) := by
    calc
      3 * (3 ^ D.tailLength) + D.prependGap
          = 3 ^ D.tailLength * 3 + D.prependGap := by
              rw [Nat.mul_comm 3 (3 ^ D.tailLength)]
      _ = 2 * (2 ^ D.tailExponent) := hprepend'
  omega

/-- natural packet の二つの局所 half-gap と三値の線形化。 -/
structure ArithmeticData
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) where
  n : ℕ
  d : ℕ
  n_pos : 0 < n
  d_pos : 0 < d
  positiveGap :
    Word.canonicalEnd D.predecessorWord =
      Word.canonicalStart D.predecessorWord + 2 * n
  descentGap :
    Word.canonicalStart D.tailWord =
      Word.canonicalEnd D.tailWord + 2 * d
  predecessorStart_add_one :
    Word.canonicalStart D.predecessorWord + 1 = 4 * (n + d)
  tailStart_add_one :
    Word.canonicalStart D.tailWord + 1 = 6 * (n + d)
  endpoint_add_one :
    Word.canonicalEnd D.tailWord + 1 = 6 * n + 4 * d

/--
predecessor word は tail word の先頭に `1` を付けたもの。
-/
theorem predecessorWord_eq_cons_tailWord
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.predecessorWord = 1 :: D.tailWord := by
  simpa [predecessorWord, tailWord] using D.suffix_eq


/--
predecessor word と tail word は canonical endpoint を共有する。
-/
theorem predecessorWord_canonicalEnd_eq_tailWord
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.canonicalEnd D.predecessorWord =
      Word.canonicalEnd D.tailWord := by
  rw [predecessorWord, tailWord, ← D.predEnd_eq, ← D.cutEnd_eq]


/--
natural zero-replay packet の prepend-one step は
二つの canonical start を直接結ぶ。
-/
theorem predecessor_tail_headStep
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    2 * Word.canonicalStart D.tailWord =
      3 * Word.canonicalStart D.predecessorWord + 1 := by
  obtain ⟨boundary, hReplay⟩ :=
    D.exists_prependOneReplayData_zero
  have hboundary :
      boundary = Word.canonicalStart D.tailWord := by
    have h := hReplay.boundary_eq
    simpa [tailWord] using h
  have hhead :
      2 * Word.canonicalStart D.tailWord =
        3 * Word.canonicalStart (1 :: D.tailWord) + 1 := by
    have h := hReplay.headStep
    rw [hboundary] at h
    simpa [tailWord] using h
  rw [D.predecessorWord_eq_cons_tailWord]
  exact hhead

/--
natural packet の positive gap と descent gap を
正の半差 `n,d` で表す。
-/
theorem exists_positive_descent_coordinates
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ∃ n d : ℕ,
      0 < n ∧
      0 < d ∧
      Word.canonicalEnd D.predecessorWord =
        Word.canonicalStart D.predecessorWord + 2 * n ∧
      Word.canonicalStart D.tailWord =
        Word.canonicalEnd D.tailWord + 2 * d := by
  obtain ⟨a, haRaw⟩ :=
    O.value_odd (R.startIndex + D.pred)
  obtain ⟨b, hbRaw⟩ :=
    O.value_odd (R.startIndex + F.length)
  obtain ⟨c, hcRaw⟩ :=
    O.value_odd (R.startIndex + D.cut)
  have ha :
      boundaryValue F D.pred = 2 * a + 1 := by
    simpa [boundaryValue, two_mul] using haRaw
  have hb :
      F.endpointValue = 2 * b + 1 := by
    simpa [FirstCrossingData.endpointValue, two_mul] using hbRaw
  have hc :
      boundaryValue F D.cut = 2 * c + 1 := by
    simpa [boundaryValue, two_mul] using hcRaw
  have hab : a < b := by
    have h := D.pred_boundary_lt_endpoint
    rw [ha, hb] at h
    omega
  have hbc : b < c := by
    have hstrict := D.tail_strict_descent
    have hactual :
        F.endpointValue < boundaryValue F D.cut := by
      rw [D.cutEnd_eq, D.cutStart_eq]
      simpa [tailWord] using hstrict
    rw [hb, hc] at hactual
    omega
  let n := b - a
  let d := c - b
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hPositiveActual :
      F.endpointValue =
        boundaryValue F D.pred + 2 * n := by
    rw [ha, hb]
    dsimp [n]
    omega
  have hDescentActual :
      boundaryValue F D.cut =
        F.endpointValue + 2 * d := by
    rw [hb, hc]
    dsimp [d]
    omega
  have hPositive :
      Word.canonicalEnd D.predecessorWord =
        Word.canonicalStart D.predecessorWord + 2 * n := by
    rw [
      predecessorWord,
      ← D.predEnd_eq,
      ← D.predStart_eq
    ]
    exact hPositiveActual
  have hDescent :
      Word.canonicalStart D.tailWord =
        Word.canonicalEnd D.tailWord + 2 * d := by
    rw [
      tailWord,
      ← D.cutStart_eq,
      ← D.cutEnd_eq
    ]
    exact hDescentActual
  exact ⟨n, d, hn, hd, hPositive, hDescent⟩

/--
positive gap と descent gap、および prepend-one head-step から
三つの canonical value を `n,d` の線形式へ落とす。
-/
theorem linear_identities_of_positive_descent_coordinates
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {n d : ℕ}
    (hPositive :
      Word.canonicalEnd D.predecessorWord =
        Word.canonicalStart D.predecessorWord + 2 * n)
    (hDescent :
      Word.canonicalStart D.tailWord =
        Word.canonicalEnd D.tailWord + 2 * d) :
    Word.canonicalStart D.predecessorWord + 1 =
        4 * (n + d) ∧
    Word.canonicalStart D.tailWord + 1 =
        6 * (n + d) ∧
    Word.canonicalEnd D.tailWord + 1 =
        6 * n + 4 * d := by
  have hhead := D.predecessor_tail_headStep
  have hend :=
    D.predecessorWord_canonicalEnd_eq_tailWord
  constructor
  · omega
  constructor <;> omega

/--
natural packet から ArithmeticData が存在する。
-/
theorem arithmeticData_nonempty
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nonempty (ArithmeticData D) := by
  obtain ⟨n, d, hn, hd, hPositive, hDescent⟩ :=
    D.exists_positive_descent_coordinates
  obtain ⟨hS, hs, ht⟩ :=
    D.linear_identities_of_positive_descent_coordinates
      hPositive hDescent
  exact ⟨{
    n := n
    d := d
    n_pos := hn
    d_pos := hd
    positiveGap := hPositive
    descentGap := hDescent
    predecessorStart_add_one := hS
    tailStart_add_one := hs
    endpoint_add_one := ht
  }⟩

/--
natural packet から canonical な ArithmeticData を選ぶ。
-/
noncomputable def arithmeticData
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ArithmeticData D :=
  Classical.choice (arithmeticData_nonempty D)

/-- descent half-gap は `1 mod 3` ではない。 -/
theorem arithmeticData_d_mod_three_ne_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    (D.arithmeticData.d % 3) ≠ 1 := by
  intro hdmod
  have htmod : Word.canonicalEnd D.tailWord % 3 ≠ 0 := by
    intro hzero
    apply FirstCrossingData.endpoint_mod_three_ne_zero F
    rw [D.cutEnd_eq]
    simpa [tailWord] using hzero
  have hEq := D.arithmeticData.endpoint_add_one
  omega

/-- descent half-gap は少なくとも2。 -/
theorem two_le_arithmeticData_d
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    2 ≤ D.arithmeticData.d := by
  have hpos := D.arithmeticData.d_pos
  have hmod := D.arithmeticData_d_mod_three_ne_one
  omega

/-- tail canonical realization の短い exact equation。 -/
theorem tail_scaledEquation
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    2 ^ D.tailExponent * Word.canonicalEnd D.tailWord =
      3 ^ D.tailLength * Word.canonicalStart D.tailWord + D.tailAffine := by
  simpa [tailExponent, tailLength, tailAffine, Word.Realizes] using
    Word.canonicalEnd_realizes D.tailWord

/--
`B + 2*A*d = g*s`。

tail descent gap を tail affine equation に入れた exact balance。
-/
theorem tailAffine_add_twoPow_descent_eq_tailGap_mul_start
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailAffine +
        2 * (2 ^ D.tailExponent) * D.arithmeticData.d =
      D.tailGap * Word.canonicalStart D.tailWord := by
  have hreal := D.tail_scaledEquation
  have hdescent := D.arithmeticData.descentGap
  have hgap :
      3 ^ D.tailLength + D.tailGap =
        2 ^ D.tailExponent := by
    unfold tailGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [tailExponent, tailLength, Word.Contracting] using
        D.tail_contracting))
  have hdescentScaled :
      2 ^ D.tailExponent *
          Word.canonicalStart D.tailWord =
        2 ^ D.tailExponent *
            Word.canonicalEnd D.tailWord +
          2 * (2 ^ D.tailExponent) * D.arithmeticData.d := by
    rw [hdescent]
    ring
  have hgapStart :
      3 ^ D.tailLength *
          Word.canonicalStart D.tailWord +
        D.tailGap *
          Word.canonicalStart D.tailWord =
        2 ^ D.tailExponent *
          Word.canonicalStart D.tailWord := by
    calc
      3 ^ D.tailLength * Word.canonicalStart D.tailWord +
          D.tailGap * Word.canonicalStart D.tailWord
          =
        (3 ^ D.tailLength + D.tailGap) *
          Word.canonicalStart D.tailWord := by
            ring
      _ =
        2 ^ D.tailExponent *
          Word.canonicalStart D.tailWord := by
            rw [hgap]
  nlinarith
/--
`B + g = 6*n*g + 2*d*G`。
natural sign-change の first exact affine identity。
-/
theorem tailAffine_add_tailGap_eq_six_n_gap_add_two_d_prependGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailAffine + D.tailGap =
      6 * D.arithmeticData.n * D.tailGap +
        2 * D.arithmeticData.d * D.prependGap := by
  have hB := D.tailAffine_add_twoPow_descent_eq_tailGap_mul_start
  have hs := D.arithmeticData.tailStart_add_one
  have hgap := D.three_mul_tailGap_eq_twoPow_add_prependGap
  nlinarith

/--
`3*B + A = G*s + 6*n*A`。
natural sign-change の第二 exact affine identity。
-/
theorem three_mul_tailAffine_add_twoPow_eq_prependGap_mul_start_add_six_n_twoPow
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    3 * D.tailAffine + 2 ^ D.tailExponent =
      D.prependGap * Word.canonicalStart D.tailWord +
        6 * D.arithmeticData.n * (2 ^ D.tailExponent) := by
  have hE1 :=
    D.tailAffine_add_tailGap_eq_six_n_gap_add_two_d_prependGap
  have hs := D.arithmeticData.tailStart_add_one
  have hgap := D.three_mul_tailGap_eq_twoPow_add_prependGap
  have hB := D.tailAffine_add_twoPow_descent_eq_tailGap_mul_start
  nlinarith

/-- natural tail の exact all-suffix gap budget。 -/
theorem exact_suffixGapBudget
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    (D.tailLength + 1) * 2 ^ D.tailExponent =
      D.prependGap * Word.canonicalStart D.tailWord +
        6 * D.arithmeticData.n * (2 ^ D.tailExponent) +
          Word.suffixGapBudget D.tailWord := by
  have hBudget0 :=
    Word.AllSuffixesContracting.oddSteps_mul_twoPow_eq_three_mul_affine_add_suffixGapBudget
        D.tail_allSuffixesContracting
  have hBudget :
      D.tailLength * 2 ^ D.tailExponent =
        3 * D.tailAffine + Word.suffixGapBudget D.tailWord := by
    simpa [tailLength, tailExponent, tailAffine] using hBudget0
  have hAffine :=
    D.three_mul_tailAffine_add_twoPow_eq_prependGap_mul_start_add_six_n_twoPow
  calc
    (D.tailLength + 1) * 2 ^ D.tailExponent
        = D.tailLength * 2 ^ D.tailExponent +
            2 ^ D.tailExponent := by ring
    _ =
        (3 * D.tailAffine + Word.suffixGapBudget D.tailWord) +
          2 ^ D.tailExponent := by
            rw [hBudget]
    _ =
        (3 * D.tailAffine + 2 ^ D.tailExponent) +
          Word.suffixGapBudget D.tailWord := by ring
    _ =
        (D.prependGap * Word.canonicalStart D.tailWord +
            6 * D.arithmeticData.n * (2 ^ D.tailExponent)) +
          Word.suffixGapBudget D.tailWord := by
            rw [hAffine]
    _ =
        D.prependGap * Word.canonicalStart D.tailWord +
          6 * D.arithmeticData.n * (2 ^ D.tailExponent) +
            Word.suffixGapBudget D.tailWord := by ring

/-- exact budget から `6*n <= tailLength`。 -/
theorem six_mul_n_le_tailLength
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    6 * D.arithmeticData.n ≤ D.tailLength := by
  have hEq := D.exact_suffixGapBudget
  have hApos : 0 < 2 ^ D.tailExponent :=
    Nat.pow_pos (by omega)
  have hGpos : 0 < D.prependGap := D.prependGap_pos
  have hspos : 0 < Word.canonicalStart D.tailWord := by
    unfold tailWord
    rw [← D.cutStart_eq]
    unfold boundaryValue
    exact O.value_pos _
  have hEpos : 0 < Word.suffixGapBudget D.tailWord :=
    Word.AllSuffixesContracting.suffixGapBudget_pos
      D.tail_allSuffixesContracting D.tail_nonempty
  have hlt :
      6 * D.arithmeticData.n * (2 ^ D.tailExponent) <
        (D.tailLength + 1) * 2 ^ D.tailExponent := by
    nlinarith
  have hlt' : 6 * D.arithmeticData.n < D.tailLength + 1 := by
    exact (Nat.mul_lt_mul_right hApos).mp (by
      simpa [Nat.mul_assoc] using hlt)
  omega

/--
`(tailLength, tailExponent, tailAffine)` が同じ valid word は natural tail 自身しかない。
affine decoder により、指定された三つ組から候補 word は高々一つ。
-/
theorem tailWord_unique_of_invariants
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {w : Collatz.Word}
    (hvalid : Word.Valid w)
    (hm : Word.oddSteps w = D.tailLength)
    (hJ : Word.twoSteps w = D.tailExponent)
    (hB : Word.affineConst w = D.tailAffine) :
    w = D.tailWord := by
  apply Word.valid_word_unique_of_oddSteps_twoSteps_affineConst
    hvalid D.tail_valid
  · simpa [tailLength] using hm
  · simpa [tailExponent] using hJ
  · simpa [tailAffine] using hB

/--
`G*s + 6*n*A < (m+1)A`。
all-suffix gap budget が正であることを残した near-resonance inequality。
-/
theorem prependGap_mul_start_add_six_n_twoPow_lt
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.prependGap * Word.canonicalStart D.tailWord +
        6 * D.arithmeticData.n * (2 ^ D.tailExponent) <
      (D.tailLength + 1) * 2 ^ D.tailExponent := by
  have hEq := D.exact_suffixGapBudget
  have hBudgetPos :=
    Word.AllSuffixesContracting.suffixGapBudget_pos
      D.tail_allSuffixesContracting D.tail_nonempty
  omega

end FirstCrossingData.NaturalZeroReplaySignChangeData
end PositiveReturn
end AdjacentReturn
end Collatz
