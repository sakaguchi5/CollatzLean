import CollatzLean.Collatz.AdjacentReturn.Basic
import CollatzLean.Collatz.Word.Contracting
import CollatzLean.Collatz.OddOrbit.FutureMinimumArithmetic

/-!
# adjacent return geometry

標準future-minimum列の隣接性を使い、任意の真の内部位置から次minimumまでの
actual suffixがcontractingであることをState APIへ戻す。
このsuffix geometryはExpanding/Contractingの枝に依存しない。
-/

namespace Collatz
namespace AdjacentReturn

/-- actual segmentの各開始offsetから終点までcontractingなら全suffix contracting。 -/
theorem allSuffixesContracting_segment
    (O : OddOrbit) {i q : ℕ}
    (h : ∀ k : ℕ, k < q →
      (O.segment (i + k) (q - k)).Contracting) :
    (O.segment i q).AllSuffixesContracting := by
  induction q generalizing i with
  | zero => simp [Word.AllSuffixesContracting]
  | succ q ih =>
      rw [O.segment_succ]
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

namespace State

/-- 隣接wordの先頭`k`個はactual prefix segment。 -/
theorem word_take_eq_segment
    {O : OddOrbit} (R : State O) {k : ℕ} (hk : k ≤ R.length) :
    R.word.take k = O.segment R.startIndex k := by
  unfold word
  exact O.segment_take_of_le hk

/-- 隣接wordを位置`k`でactual prefix/suffixへ分解する。 -/
theorem word_eq_prefix_append_suffix
    {O : OddOrbit} (R : State O) {k : ℕ} (hk : k ≤ R.length) :
    R.word =
      O.segment R.startIndex k ++
      O.segment (R.startIndex + k) (R.length - k) := by
  unfold word
  have hlen : R.length = k + (R.length - k) := by
    omega
  calc
    O.segment R.startIndex R.length
        = O.segment R.startIndex (k + (R.length - k)) := by
            congr 1
    _ = O.segment R.startIndex k ++
        O.segment (R.startIndex + k) (R.length - k) := by
          exact O.segment_add R.startIndex k (R.length - k)

/-- current future minimumのactual exponentは1。 -/
theorem startExponent_eq_one
    {O : OddOrbit} (R : State O) : O.exponent R.startIndex = 1 := by
  exact R.startFutureMinimum.exponent_eq_one R.unbounded

/-- next future minimumのactual exponentも1。 -/
theorem nextExponent_eq_one
    {O : OddOrbit} (R : State O) : O.exponent R.nextIndex = 1 := by
  exact R.nextFutureMinimum.exponent_eq_one R.unbounded

/-- 隣接future-minimum値差は4の正倍数。 -/
theorem valueGap_four_dvd
    {O : OddOrbit} (R : State O) : ∃ q : ℕ, R.valueGap = 4 * q := by
  have h := OddOrbit.four_dvd_value_gap_of_exponent_one O
    R.startValue_lt_nextValue R.startExponent_eq_one R.nextExponent_eq_one
  simpa [startValue, nextValue, valueGap] using h

/-- 隣接future-minimum値差は少なくとも4。 -/
theorem four_le_valueGap
    {O : OddOrbit} (R : State O) : 4 ≤ R.valueGap := by
  obtain ⟨q, hq⟩ := R.valueGap_four_dvd
  have hpos := R.valueGap_pos
  rw [hq] at hpos ⊢
  have hqpos : 0 < q := by omega
  omega

/-- 次future-minimum値はcurrentより後の任意のendpoint以下。 -/
theorem nextValue_le_positiveEndpoint
    {O : OddOrbit} (R : State O) (p : ℕ) (hp : 0 < p) :
    R.nextValue ≤ O.value (R.startIndex + p) := by
  unfold nextValue
  exact R.standard R.index (R.startIndex + p) (by
    unfold startIndex
    omega)

/-- currentから任意の正長endpointまでの正差は隣接値差以上。 -/
theorem valueGap_le_endpointGap
    {O : OddOrbit} (R : State O) {p : ℕ}
    (hp : 0 < p)
    (hstart : R.startValue ≤ O.value (R.startIndex + p)) :
    R.valueGap ≤ O.value (R.startIndex + p) - R.startValue := by
  have hnext := R.nextValue_le_positiveEndpoint p hp
  rw [R.nextValue_eq_startValue_add_valueGap] at hnext
  omega

/-- 任意の真のproper suffixは次future-minimumへ真に下がるためcontracting。 -/
theorem properSuffix_contracting
    {O : OddOrbit} (R : State O) {k : ℕ}
    (hkPos : 0 < k) (hkLt : k < R.length) :
    (O.segment (R.startIndex + k) (R.length - k)).Contracting := by
  have hleft : R.startIndex < R.startIndex + k := by omega
  have htail :
      O.value R.nextIndex ≤ O.value (R.startIndex + k) := by
    exact R.standard R.index (R.startIndex + k) hleft
  have hright : R.startIndex + k < R.nextIndex := by
    rw [R.nextIndex_eq_startIndex_add_length]
    omega
  have hne : O.value (R.startIndex + k) ≠ O.value R.nextIndex := by
    exact O.value_ne_of_lt_of_unbounded R.unbounded hright
  have hdec : O.value R.nextIndex < O.value (R.startIndex + k) := by omega
  have hlenPos : 0 < R.length - k := by omega
  have hend : R.startIndex + k + (R.length - k) = R.nextIndex := by
    rw [R.nextIndex_eq_startIndex_add_length]
    omega
  have hrun := O.realizesSegment (R.startIndex + k) (R.length - k)
  have hvalid := (O.runsSegment (R.startIndex + k) (R.length - k)).valid
  have hneWord : O.segment (R.startIndex + k) (R.length - k) ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  apply hrun.contracting_of_start_gt_end hvalid hneWord
  rw [hend]
  exact hdec

/--
任意の真のproper suffixでは、そのsuffix自身の全非空suffixもcontracting。
標準future-minimumの隣接性だけを用い、枝には依存しない。
-/
theorem properSuffix_allSuffixesContracting
    {O : OddOrbit} (R : State O) {k : ℕ}
    (hkPos : 0 < k) (hkLt : k < R.length) :
    (O.segment (R.startIndex + k) (R.length - k)).AllSuffixesContracting := by
  apply allSuffixesContracting_segment O
  intro j hj
  have hkjPos : 0 < k + j := by omega
  have hkjLt : k + j < R.length := by omega
  have hs := R.properSuffix_contracting
    (k := k + j) hkjPos hkjLt
  have hindex : R.startIndex + (k + j) = R.startIndex + k + j := by omega
  have hlen : R.length - (k + j) = (R.length - k) - j := by omega
  rw [hindex, hlen] at hs
  exact hs

/--
長さ2以上の標準adjacent returnでは、先頭を除いたactual tailの
全非空suffixがcontracting。枝には依存しない。
-/
theorem tail_allSuffixesContracting
    {O : OddOrbit} (R : State O) (hlen : 1 < R.length) :
    (O.segment (R.startIndex + 1) (R.length - 1)).AllSuffixesContracting := by
  exact R.properSuffix_allSuffixesContracting
    (k := 1) (by omega) hlen

/-- 正長隣接wordを先頭exponentとactual tailへ分解する。 -/
theorem word_eq_startExponent_cons_tail
    {O : OddOrbit} (R : State O) :
    R.word = O.exponent R.startIndex ::
      O.segment (R.startIndex + 1) (R.length - 1) := by
  have hpos := R.length_pos
  obtain ⟨q, hq⟩ : ∃ q : ℕ, R.length = q + 1 :=
    ⟨R.length - 1, by omega⟩
  unfold word
  rw [hq]
  simp only [O.segment_succ]
  rw [show q + 1 - 1 = q by omega]

/-- expanding adjacent returnでは全proper prefixがexpanding。 -/
theorem properPrefixesExpanding
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding) :
    R.word.ProperPrefixesExpanding := by
  intro k hkPos hkLtWord
  have hkLt : k < R.length := by simpa using hkLtWord
  have hkLe : k ≤ R.length := Nat.le_of_lt hkLt
  have htake := R.word_take_eq_segment hkLe
  have hvalid : (O.segment R.startIndex k).Valid :=
    (O.runsSegment R.startIndex k).valid
  have hne : O.segment R.startIndex k ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  rcases Word.expanding_or_contracting_of_valid_nonempty hvalid hne with hExp | hCon
  · rw [htake]
    exact hExp
  · have hSuffix := R.properSuffix_contracting hkPos hkLt
    have hWholeCon : R.word.Contracting := by
      rw [R.word_eq_prefix_append_suffix hkLe]
      exact hCon.append hSuffix
    unfold IsExpanding Word.Expanding at hE
    unfold Word.Contracting at hWholeCon
    omega

/-- contracting adjacent returnではwholeを含む全非空suffixがcontracting。 -/
theorem allSuffixesContracting
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    R.word.AllSuffixesContracting := by
  change (O.segment R.startIndex R.length).AllSuffixesContracting
  apply allSuffixesContracting_segment O
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simpa [IsContracting, word] using hC
  · exact R.properSuffix_contracting (Nat.pos_of_ne_zero hk0) hk

end State
end AdjacentReturn
end Collatz
