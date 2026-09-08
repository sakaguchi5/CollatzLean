import CollatzLean.Collatz3.Critical.FirstPassage
import CollatzLean.Collatz3.Critical.ProfileAffine
import CollatzLean.Collatz3.Core.PrefixAffine

import Mathlib.Data.Fintype.BigOperators

/-!
# Collatz3: word から finite critical profile を抽出

critical first-passage word の各 odd cut に対し

`depth_k = beattyIndex k - prefixTwoDepth w k`

を取る。profile は常に有限関数 `Fin m → ℕ` であり、
actuality はこのファイルに持ち込まない。
-/

namespace Collatz3
namespace Critical

open scoped BigOperators

/-- word の prefix depth と Beatty roof の差から作る有限 profile。 -/
def profileFromWord
    (w : Word) : Profile (Word.oddSteps w) :=
  fun k => beattyIndex k.1 - Word.prefixTwoDepth w k.1

/-- 抽出 profile の depth は自動的に Beatty roof 以下。 -/
theorem profileFromWord_depth_le
    (w : Word)
    (k : Fin (Word.oddSteps w)) :
    profileFromWord w k ≤ beattyIndex k.1 := by
  unfold profileFromWord
  omega

/-- first-passage 条件下では profile checkpoint が元の prefix depth に exact に戻る。 -/
theorem checkpoint_profileFromWord_eq_prefixTwoDepth
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w)
    (k : Fin (Word.oddSteps w)) :
    checkpoint (profileFromWord w) k =
      Word.prefixTwoDepth w k.1 := by
  have hRoof :
      Word.prefixTwoDepth w k.1 ≤ beattyIndex k.1 :=
    hFirst.prefixDepth_le_beatty k.2
  unfold checkpoint profileFromWord
  omega

/-- valid critical first-passage word から得る profile は admissible。 -/
theorem profileFromWord_admissible
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w)
    (hValid : Word.Valid w) :
    Admissible (profileFromWord w) := by
  constructor
  · intro k
    exact profileFromWord_depth_le w k
  · intro k hk
    rw [checkpoint_profileFromWord_eq_prefixTwoDepth hFirst
      ⟨k, by omega⟩]
    rw [checkpoint_profileFromWord_eq_prefixTwoDepth hFirst
      ⟨k + 1, hk⟩]
    exact Word.prefixTwoDepth_strict_succ_of_valid
      hValid (by omega)

/-- first-passage profile の affine numerator は word の prefix numerator と一致。 -/
theorem profileAffineNumerator_profileFromWord_eq
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w) :
    profileAffineNumerator (profileFromWord w) =
      Word.affinePrefixNumerator w := by
  calc
    profileAffineNumerator (profileFromWord w)
        =
        ∑ k : Fin (Word.oddSteps w),
          2 ^ Word.prefixTwoDepth w k.1 *
            3 ^ (Word.oddSteps w - (k.1 + 1)) := by
              unfold profileAffineNumerator profileAffineTerm
              apply Finset.sum_congr rfl
              intro k hk
              rw [checkpoint_profileFromWord_eq_prefixTwoDepth hFirst k]
    _ =
        ∑ k ∈ Finset.range (Word.oddSteps w),
          2 ^ Word.prefixTwoDepth w k *
            3 ^ (Word.oddSteps w - (k + 1)) := by
              exact Fin.sum_univ_eq_sum_range
                (fun k =>
                  2 ^ Word.prefixTwoDepth w k *
                    3 ^ (Word.oddSteps w - (k + 1)))
                (Word.oddSteps w)
    _ = Word.affinePrefixNumerator w := by
      rfl

/-- first-passage profile の affine numerator は元 word の `affineConst` そのもの。 -/
theorem profileAffineNumerator_profileFromWord_eq_affineConst
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w) :
    profileAffineNumerator (profileFromWord w) =
      Word.affineConst w := by
  rw [profileAffineNumerator_profileFromWord_eq hFirst]
  exact Word.affinePrefixNumerator_eq_affineConst w

end Critical
end Collatz3
