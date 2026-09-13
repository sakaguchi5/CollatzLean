import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersBasisBound

/-!
# Collatz3 Experimental2: basis 面積の parity obstruction

同じ successive rank vector を持つ Frobenius symbol の weight は

  D + 2 Σ arms - Σ ranks

なので、basis weight との差は必ず `2` の倍数になる。
RecordFerrers へ戻すと actual Young cell count と basis weight は同じ parity を持つ。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 同一 rank vector では任意 arm weight と basis weight の差は2倍。 -/
theorem symbolWeightZ_sub_basisWeightZ
    (ranks arms : List ℤ) :
    symbolWeightZ ranks arms - basisWeightZ ranks =
      2 * (arms.sum - (basisArms ranks).sum) := by
  simp [symbolWeightZ, basisWeightZ]
  ring

/-- actual Young 面積と basis weight の差は偶数。 -/
theorem codeArea_sub_basisWeightZ_eq_two_mul
    (c : WidthDropCode) :
    ∃ k : ℤ,
      (codeArea c : ℤ) - basisWeightZ (successiveRankVector c) = 2 * k := by
  refine ⟨(frobeniusArmsZ c).sum -
      (basisArms (successiveRankVector c)).sum, ?_⟩
  rw [← frobeniusSymbolWeight_eq_codeArea c]
  exact symbolWeightZ_sub_basisWeightZ
    (successiveRankVector c) (frobeniusArmsZ c)

/-- F6: modulo `2` で actual area と basis weight は一致する。 -/
theorem codeArea_sub_basisWeightZ_emod_two
    (c : WidthDropCode) :
    ((codeArea c : ℤ) - basisWeightZ (successiveRankVector c)) % 2 = 0 := by
  rcases codeArea_sub_basisWeightZ_eq_two_mul c with ⟨k, hk⟩
  rw [hk]
  simp

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers の actual Young 面積と basis weight の差は2倍。 -/
theorem youngCellCount_sub_basisWeightZ_eq_two_mul
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    ∃ k : ℤ,
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks = 2 * k := by
  unfold youngCellCount successiveRanks
  exact codeArea_sub_basisWeightZ_eq_two_mul R.plateauWidthDropCode

/-- F6 の合同条件。 -/
theorem youngCellCount_sub_basisWeightZ_emod_two
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    ((R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks) % 2 = 0 := by
  rcases R.youngCellCount_sub_basisWeightZ_eq_two_mul with ⟨k, hk⟩
  rw [hk]
  simp

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
