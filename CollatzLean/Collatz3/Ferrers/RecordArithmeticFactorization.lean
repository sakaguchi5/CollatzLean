import CollatzLean.Collatz3.Ferrers.RecordWordFactorization
import CollatzLean.Collatz3.Core.WordTransfer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Collatz3: RecordFerrers の width / depth / Beatty / affine factorization

7 で得た lossless word factorization を算術へ移す。

* width `m` は固定 prefix `1` と canonical block widths の和へ分解される。
* total two-depth `H_m` も固定 head depth `1` と各 local critical depth `H_r` の和へ分解される。
* 従って Beatty index の加法欠損は canonical block 個数そのものになる。
* affine translation `B` は local word 列の composition fold に exact に分解される。

ここでも primitive / best-upper は使わない。
-/

namespace Collatz3
namespace Ferrers

open Critical

/-- word 列全体の odd-step 数の和。 -/
def wordsOddSteps (ws : List Word) : ℕ :=
  (ws.map Word.oddSteps).sum

/-- word 列全体の two-depth の和。 -/
def wordsTwoSteps (ws : List Word) : ℕ :=
  (ws.map Word.twoSteps).sum

/--
word 列を左から affine composition したときの translation。
`affineConst (ws.flatten)` を block summary だけで再帰的に書いたもの。
-/
def affineConstBlocks : List Word → ℕ
  | [] => 0
  | w :: ws =>
      3 ^ wordsOddSteps ws * Word.affineConst w +
        2 ^ Word.twoSteps w * affineConstBlocks ws

/-- flatten した word の odd-step 数は各 block の odd-step 数の和。 -/
theorem oddSteps_flatten_eq_wordsOddSteps :
    ∀ ws : List Word,
      Word.oddSteps ws.flatten = wordsOddSteps ws
  | [] => by
      simp [wordsOddSteps]
  | w :: ws => by
      simp [wordsOddSteps, oddSteps_flatten_eq_wordsOddSteps ws,Nat.add_comm]

/-- flatten した word の two-depth は各 block の two-depth の和。 -/
theorem twoSteps_flatten_eq_wordsTwoSteps :
    ∀ ws : List Word,
      Word.twoSteps ws.flatten = wordsTwoSteps ws
  | [] => by
      simp [wordsTwoSteps]
  | w :: ws => by
      simp [wordsTwoSteps, twoSteps_flatten_eq_wordsTwoSteps ws, Nat.add_comm]

/-- affine block fold は flatten 後の `affineConst` と exact に一致する。 -/
theorem affineConst_flatten_eq_affineConstBlocks :
    ∀ ws : List Word,
      Word.affineConst ws.flatten = affineConstBlocks ws
  | [] => by
      simp [affineConstBlocks]
  | w :: ws => by
      simp only [List.flatten_cons]
      rw [Word.affineConst_append]
      rw [oddSteps_flatten_eq_wordsOddSteps]
      rw [affineConst_flatten_eq_affineConstBlocks]
      rfl

/-- local critical block 列では local word の two-depth は各 `criticalTwoDepth r` に一致する。 -/
theorem wordsTwoSteps_localWordsFromLengths_eq_sum_criticalTwoDepth
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (rs : List ℕ),
      LocalCriticalBlocksFrom h a rs →
      wordsTwoSteps (localWordsFromLengths h a rs) =
        (rs.map criticalTwoDepth).sum
  | _a, [], _L => by
      simp [wordsTwoSteps, localWordsFromLengths]
  | a, r :: rs, L => by
      have hHead :=
        (isCriticalWord_localWord A L.1).twoSteps_eq
      have hTail :=
        wordsTwoSteps_localWordsFromLengths_eq_sum_criticalTwoDepth
          A (a + r) rs L.2
      have hTail' :
          (List.map Word.twoSteps
              (localWordsFromLengths h (a + r) rs)).sum =
            (rs.map criticalTwoDepth).sum := by
        simpa [wordsTwoSteps] using hTail
      simp [wordsTwoSteps, localWordsFromLengths, hHead, hTail']

/-- `criticalTwoDepth r = beattyIndex r + 1` を list 全体で加算した形。 -/
theorem sum_criticalTwoDepth_eq_sum_beattyIndex_add_length :
    ∀ rs : List ℕ,
      (rs.map criticalTwoDepth).sum =
        (rs.map beattyIndex).sum + rs.length
  | [] => by simp
  | r :: rs => by
      simp [criticalTwoDepth,
        sum_criticalTwoDepth_eq_sum_beattyIndex_add_length rs]
      omega

namespace RecordFerrers

/-- canonical block widths は fixed head width `1` と合わせて whole width `m` を exact に覆う。 -/
theorem width_eq_one_add_sum_canonicalRecordLengths
    {m : ℕ}
    (R : RecordFerrers m) :
    m = 1 + (canonicalRecordLengths R.profile.1).sum := by
  have hSum :=
    canonicalRecordLengths_sum (h := R.profile.1) R.one_lt_width
  have hmPos : 0 < m := by
    exact lt_trans Nat.zero_lt_one R.one_lt_width
  omega

/-- canonical block width は必ず whole width より strict に小さい。 -/
theorem canonicalRecordLength_lt_width
    {m : ℕ}
    (R : RecordFerrers m)
    {r : ℕ}
    (hr : r ∈ canonicalRecordLengths R.profile.1) :
    r < m := by
  have hLe :
      r ≤ (canonicalRecordLengths R.profile.1).sum :=
    List.le_sum_of_mem hr
  have hSum :=
    canonicalRecordLengths_sum (h := R.profile.1) R.one_lt_width
  have hmPos : 0 < m := by
    exact lt_trans Nat.zero_lt_one R.one_lt_width
  omega

/-- canonical local words の total odd-step 数は `m-1`。 -/
theorem wordsOddSteps_canonicalLocalWords
    {m : ℕ}
    (R : RecordFerrers m) :
    wordsOddSteps R.canonicalLocalWords = m - 1 := by
  unfold wordsOddSteps
  rw [R.map_oddSteps_canonicalLocalWords]
  exact canonicalRecordLengths_sum
    (h := R.profile.1) R.one_lt_width

/-- canonical local words の total two-depth は各 local critical depth の和。 -/
theorem wordsTwoSteps_canonicalLocalWords
    {m : ℕ}
    (R : RecordFerrers m) :
    wordsTwoSteps R.canonicalLocalWords =
      ((canonicalRecordLengths R.profile.1).map criticalTwoDepth).sum := by
  exact
    wordsTwoSteps_localWordsFromLengths_eq_sum_criticalTwoDepth
      R.profile.2 initialRoofAnchor
      (canonicalRecordLengths R.profile.1)
      R.localCriticalBlocks

/--
whole critical depth は fixed head depth `1` と canonical block critical depths の和。

`H_m = 1 + Σ H_{r_i}`。
-/
theorem criticalTwoDepth_eq_one_add_sum_blockDepths
    {m : ℕ}
    (R : RecordFerrers m) :
    criticalTwoDepth m =
      1 + ((canonicalRecordLengths R.profile.1).map criticalTwoDepth).sum := by
  have hmPos : 0 < m := by
    exact lt_trans Nat.zero_lt_one R.one_lt_width
  have hmPos : 0 < m := by omega
  have hWhole :
      Word.twoSteps (wordOfProfile R.profile.1) = criticalTwoDepth m :=
    twoSteps_wordOfProfile R.profile.2 hmPos
  have hFactor :=
    R.wordOfProfile_eq_one_append_flatten_canonicalLocalWords
  have hDepthFactor := congrArg Word.twoSteps hFactor
  have hFlat :=
    twoSteps_flatten_eq_wordsTwoSteps R.canonicalLocalWords
  have hBlocks := R.wordsTwoSteps_canonicalLocalWords
  rw [Word.twoSteps_append] at hDepthFactor
  simp only [Word.twoSteps_cons, Word.twoSteps_nil, add_zero] at hDepthFactor
  rw [hFlat, hBlocks] at hDepthFactor
  omega

/--
Beatty index の加法欠損は canonical record block 個数に exact に一致する。

`β(m) = Σ β(r_i) + numberOfBlocks`。
-/
theorem beattyIndex_eq_sum_blockBeatty_add_blockCount
    {m : ℕ}
    (R : RecordFerrers m) :
    beattyIndex m =
      ((canonicalRecordLengths R.profile.1).map beattyIndex).sum +
        (canonicalRecordLengths R.profile.1).length := by
  have hDepth := R.criticalTwoDepth_eq_one_add_sum_blockDepths
  have hExpand :=
    sum_criticalTwoDepth_eq_sum_beattyIndex_add_length
      (canonicalRecordLengths R.profile.1)
  rw [hExpand] at hDepth
  unfold criticalTwoDepth at hDepth
  omega

/-- canonical local word 列の affine translation を block composition fold で読む。 -/
theorem affineConst_flatten_canonicalLocalWords
    {m : ℕ}
    (R : RecordFerrers m) :
    Word.affineConst R.canonicalLocalWords.flatten =
      affineConstBlocks R.canonicalLocalWords :=
  affineConst_flatten_eq_affineConstBlocks R.canonicalLocalWords

/--
whole profile word の affine translation `B` は

`B_whole = 3^(m-1) + 2 * B_blocks`

と exact に分解される。`B_blocks` は各 canonical local word の affine translation を
正しい 3/2 weight で合成した `affineConstBlocks`。
-/
theorem affineConst_wordOfProfile_eq_head_add_two_mul_blocks
    {m : ℕ}
    (R : RecordFerrers m) :
    Word.affineConst (wordOfProfile R.profile.1) =
      3 ^ (m - 1) + 2 * affineConstBlocks R.canonicalLocalWords := by
  have hFactor :=
    R.wordOfProfile_eq_one_append_flatten_canonicalLocalWords
  have hB := congrArg Word.affineConst hFactor
  rw [Word.affineConst_append] at hB
  have hOdd := R.wordsOddSteps_canonicalLocalWords
  have hFlat := R.affineConst_flatten_canonicalLocalWords
  have hHeadB : Word.affineConst ([1] : Word) = 1 := by
    norm_num [Word.affineConst_cons, Word.oddSteps]
  have hHeadH : Word.twoSteps ([1] : Word) = 1 := by
    norm_num [Word.twoSteps]
  rw [oddSteps_flatten_eq_wordsOddSteps, hOdd, hFlat, hHeadB, hHeadH] at hB
  norm_num at hB ⊢
  exact hB

end RecordFerrers
end Ferrers
end Collatz3
