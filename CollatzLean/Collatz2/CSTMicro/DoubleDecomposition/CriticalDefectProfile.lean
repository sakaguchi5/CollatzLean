import CollatzLean.Collatz2.Geometry.CriticalProfile

/-!
# valid minimal crossing block と critical defect profile

Record 側では exponent word そのものより、各 proper cut が critical roof から
何段下にあるかを構成データとして使いたい。

  defect(k) = criticalHeight(k) - prefixTwoDepth(w,k)

ここでは FirstCrossing の条件を、この defect が subtraction で情報を失わず

  prefixTwoDepth(w,k) + defect(k) = criticalHeight(k)

と復元できることへ exact に言い換える。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/-- valid な first-crossing word を「minimal crossing block」として束ねる。 -/
def ValidMinimalCrossingBlock (w : Word) : Prop :=
  w.Valid ∧ Word.FirstCrossing w

/--
構成側 Record/Ferrers が保持すべき critical defect profile。

proper cut では actual depth と defect の和が critical roof そのものになる。
terminal の contracting 条件は別に保持し、proper geometry と terminal sign を混ぜない。
-/
def AdmissibleCriticalDefectProfile (w : Word) : Prop :=
  w.Valid ∧
    w ≠ [] ∧
    (∀ k : ℕ, 0 < k → k < Word.oddSteps w →
      Word.prefixTwoDepth w k + Word.criticalDefect w k =
        Word.criticalHeight k) ∧
    Word.Contracting w

/--
valid minimal crossing block と admissible critical defect profile は同値。

この定理は Ostrowski 分解を Record 分解として使う主張ではない。
Record 側では defect profile を構成し、計算側では後続ファイルで同一区間の
重みを Christoffel/Ostrowski により評価する。
-/
theorem validMinimalCrossingBlock_iff_admissibleCriticalDefectProfile
    (w : Word) :
    ValidMinimalCrossingBlock w ↔ AdmissibleCriticalDefectProfile w := by
  constructor
  · rintro ⟨hValid, hFirst⟩
    refine ⟨hValid, hFirst.nonempty, ?_, hFirst.terminalContracting⟩
    intro k hkPos hkLt
    have hDepth :
        Word.prefixTwoDepth w k ≤ Word.criticalHeight k :=
      hFirst.prefixTwoDepth_le_criticalHeight hkPos hkLt
    unfold Word.criticalDefect
    omega
  · rintro ⟨hValid, hNonempty, hProfile, hContracting⟩
    refine ⟨hValid, ?_⟩
    refine {
      nonempty := hNonempty
      properPositive := ?_
      terminalNegative := hContracting
    }
    intro k hkPos hkLt
    have hkLtOdd : k < Word.oddSteps w := by
      simpa [Word.oddSteps] using hkLt
    have hExact := hProfile k hkPos hkLtOdd
    have hDepth :
        Word.prefixTwoDepth w k ≤ Word.criticalHeight k := by
      omega
    have hPowLe :
        2 ^ Word.prefixTwoDepth w k ≤ 2 ^ Word.criticalHeight k :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth
    have hRoof :
        2 ^ Word.criticalHeight k < 3 ^ k :=
      Word.criticalHeight_pow_lt_threePow hkPos
    have hPow :
        2 ^ Word.prefixTwoDepth w k < 3 ^ k :=
      lt_of_le_of_lt hPowLe hRoof
    have hkLe : k ≤ w.length := Nat.le_of_lt hkLt
    have hTakeLen : (w.take k).length = k :=
      List.length_take_of_le hkLe
    have hExpanding : Word.Expanding (w.take k) := by
      apply (Word.expanding_iff_twoPow_lt_threePow).2
      simpa [Word.prefixTwoDepth, Word.oddSteps, hTakeLen] using hPow
    exact hExpanding

end DoubleDecomposition
end CSTMicro
end Collatz2
