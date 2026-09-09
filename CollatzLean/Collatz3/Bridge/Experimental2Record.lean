import CollatzLean.Collatz3.Bridge.Experimental2Profile
import CollatzLean.Collatz3.Ferrers.RecordCarryBridge
import CollatzLean.Collatz3.Ferrers.RecordArithmeticFactorization
import CollatzLean.Collatz3.Experimental2.RecordBudgetCorollaries

/-!
# Collatz3 Bridge: RecordFerrers factorization を generic carry budget へ移す

`RecordFerrers` が持つ Collatz 固有情報は、canonical profile partition と
Beatty factorization を与える。

このファイルではそれを Experimental2 の一般有限 carry 理論へ渡し、

* carry 総和 = block 数 - 1
* carry `0` は一個
* terminal carry `0` を使うと pattern は `1,...,1,0`

を generic theorem の corollary として回収する。
-/

namespace Collatz3
namespace Bridge

/--
`RecordCarryCompatibleFrom` から、最後の block と terminal Beatty carry `0` を取り出す。

これは compatibility の再帰形から terminal 情報だけを忘却する補助 theorem。
-/
theorem recordCarryCompatibleFrom_exists_terminalZero
    {m : ℕ}
    {h : Critical.Profile m} :
    ∀ (a : ℕ) (rs : List ℕ),
      Critical.RecordCarryCompatibleFrom h a rs →
      ∃ pre r,
        rs = pre ++ [r] ∧
          Critical.beattyCarry (a + pre.sum) r = 0
  | _a, [], hFalse => by
      simp [Critical.RecordCarryCompatibleFrom] at hFalse
  | a, [r], C => by
      simp only [Critical.RecordCarryCompatibleFrom] at C
      exact ⟨[], r, by simp, by simpa using C.2⟩
  | a, r :: s :: rs, C => by
      simp only [Critical.RecordCarryCompatibleFrom] at C
      obtain ⟨pre, t, hTail, hZero⟩ :=
        recordCarryCompatibleFrom_exists_terminalZero
          (a + r) (s :: rs) C.2
      refine ⟨r :: pre, t, ?_, ?_⟩
      · simp [hTail]
      · simpa [Nat.add_assoc] using hZero

namespace Ferrers.RecordFerrers

/--
RecordFerrers の canonical Beatty factorization は generic carry budget `length-1` を持つ。
-/
theorem experimental2_canonicalCarrySum_eq_length_sub_one
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    (Experimental2.carryListFrom
        Critical.beattyIndex 1
        (Ferrers.canonicalRecordLengths R.profile.1)).sum =
      (Ferrers.canonicalRecordLengths R.profile.1).length - 1 := by
  exact
    beattyIndex_hasUnitCarry.normalizedFactorization_carrySum_eq_length_sub_one
      Critical.beattyIndex_one
      (Ferrers.canonicalRecordLengths R.profile.1)
      R.width_eq_one_add_sum_canonicalRecordLengths
      R.beattyIndex_eq_sum_blockBeatty_add_blockCount

/-- canonical Record block 列は常に非空。 -/
theorem canonicalRecordLengths_nonempty
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    Ferrers.canonicalRecordLengths R.profile.1 ≠ [] := by
  unfold Ferrers.canonicalRecordLengths
  exact Ferrers.blockLengthsFromCuts_ne_nil
    m Critical.initialRoofAnchor (Ferrers.initialRecordCuts R.profile.1)

/--
RecordFerrers の canonical generic carry 列には `0` が exact に一個だけある。

位置の同定にはまだ terminal compatibility を使わず、global factorization だけを使う。
-/
theorem experimental2_canonicalCarry_zeroCount_eq_one
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    (Experimental2.carryListFrom
        Critical.beattyIndex 1
        (Ferrers.canonicalRecordLengths R.profile.1)).count 0 = 1 := by
  exact
    beattyIndex_hasUnitCarry.normalizedFactorization_forces_uniqueZeroCount
      Critical.beattyIndex_one
      (Ferrers.canonicalRecordLengths R.profile.1)
      (canonicalRecordLengths_nonempty R)
      R.width_eq_one_add_sum_canonicalRecordLengths
      R.beattyIndex_eq_sum_blockBeatty_add_blockCount

/--
RecordFerrers の exact canonical carry compatibility を length 表現へ移す。
-/
theorem recordCarryCompatibleCanonicalRecordLengths
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    Critical.RecordCarryCompatibleFrom
      R.profile.1 Critical.initialRoofAnchor
      (Ferrers.canonicalRecordLengths R.profile.1) := by
  exact
    (Ferrers.canonicalCarryCompatibleFrom_iff_recordCarryCompatibleCanonicalRecordLengths
      R.one_lt_width).1 R.carryCompatible

/--
canonical Record carry 列は generic roof の語彙で exact に `1,...,1,0`。

ここで初めて terminal compatibility を使い、global budget で一意だった `0` の位置を
最後へ固定する。
-/
theorem experimental2_canonicalCarryPattern
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    ∃ pre r,
      Ferrers.canonicalRecordLengths R.profile.1 = pre ++ [r] ∧
      Experimental2.carryListFrom
          Critical.beattyIndex 1
          (Ferrers.canonicalRecordLengths R.profile.1) =
        List.replicate pre.length 1 ++ [0] := by
  obtain ⟨pre, r, hLengths, hTerminalZero⟩ :=
    recordCarryCompatibleFrom_exists_terminalZero
      Critical.initialRoofAnchor
      (Ferrers.canonicalRecordLengths R.profile.1)
      (recordCarryCompatibleCanonicalRecordLengths R)
  refine ⟨pre, r, hLengths, ?_⟩
  have hCover := R.width_eq_one_add_sum_canonicalRecordLengths
  have hFactor := R.beattyIndex_eq_sum_blockBeatty_add_blockCount
  rw [hLengths] at hCover hFactor ⊢
  have hLastZero :
      Experimental2.roofCarry Critical.beattyIndex
        (1 + pre.sum) r = 0 := by
    simpa [Critical.initialRoofAnchor] using hTerminalZero
  exact
    beattyIndex_hasUnitCarry.normalizedFactorization_forces_ones_then_zero
      Critical.beattyIndex_one pre r hCover hFactor hLastZero

end Ferrers.RecordFerrers

end Bridge
end Collatz3
