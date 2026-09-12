import CollatzLean.Collatz3.CSTMicro.OddEndpointCanonical
import CollatzLean.Collatz3.Ferrers.RecordArithmeticFactorization
import CollatzLean.Collatz3.Core.PrefixAffine
import Mathlib.Data.Fintype.BigOperators

/-!
# Collatz3 CSTMicro Stage 7A: standard path と RecordFerrers compatibility

Stage 5/6 で standard first-passage path `P` から

  endpointIndexedCriticalProfile P hp : Critical.Profile P.endpointOddCount

を canonical に得た。

ただし admissible profile が自動的に `RecordFerrers` になるわけではない。
`RecordFerrers` には deterministic `initialRecordCuts` 上の exact carry compatibility が
追加で必要である。

そこで Stage 7 ではこの追加条件を明示した branch だけを RecordFerrers geometry に入れる。
成立していない converse は仮定しない。
-/

namespace Collatz3
namespace Critical

open scoped BigOperators

/-- `IsCriticalWord` は width を消去すれば既存 `Word.CriticalFirstPassage` を与える。 -/
theorem criticalFirstPassage_of_isCriticalWord
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w) :
    Word.CriticalFirstPassage w := by
  constructor
  · rw [C.twoSteps_eq, C.oddSteps_eq]
  · intro k hk
    have hk' : k < m := by
      rw [C.oddSteps_eq] at hk
      exact hk
    exact C.prefixTwoDepth_le_beatty hk'

/--
任意の positive-width admissible profile について、profile affine numerator は
その exact exponent word `wordOfProfile` の affine translation と一致する。

RecordFerrers factorization を profile affine data へ戻すための薄い bridge。
-/
theorem profileAffineNumerator_eq_affineConst_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    profileAffineNumerator h =
      Word.affineConst (wordOfProfile h) := by
  calc
    profileAffineNumerator h
        =
        ∑ k : Fin m,
          2 ^ Word.prefixTwoDepth (wordOfProfile h) k.1 *
            3 ^ (m - (k.1 + 1)) := by
              unfold profileAffineNumerator profileAffineTerm
              apply Finset.sum_congr rfl
              intro k hk
              have hPrefix :=
                prefixTwoDepth_wordOfProfile A hm (Nat.le_of_lt k.2)
              rw [hPrefix, profileHeight_of_lt h k.2]
    _ =
        ∑ k ∈ Finset.range m,
          2 ^ Word.prefixTwoDepth (wordOfProfile h) k *
            3 ^ (m - (k + 1)) := by
              exact Fin.sum_univ_eq_sum_range
                (fun k =>
                  2 ^ Word.prefixTwoDepth (wordOfProfile h) k *
                    3 ^ (m - (k + 1)))
                m
    _ = Word.affinePrefixNumerator (wordOfProfile h) := by
          unfold Word.affinePrefixNumerator Word.affinePrefixTerm
          rw [oddSteps_wordOfProfile h]
    _ = Word.affineConst (wordOfProfile h) :=
          Word.affinePrefixNumerator_eq_affineConst (wordOfProfile h)

end Critical

namespace CSTMicro
namespace FirstPassagePath

/--
endpoint-indexed critical profile が真の RecordFerrers 条件を満たすこと。

admissibility は Stage 5 ですでに theorem なので、この predicate の新しい内容は
`1 < p` と exact canonical carry compatibility である。
-/
def RecordCompatible
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) : Prop :=
  Ferrers.IsRecordFerrersProfile
    ⟨P.endpointIndexedCriticalProfile hp,
      P.endpointIndexedCriticalProfile_admissible hp⟩

/-- Record-compatible standard path から canonical RecordFerrers を得る。 -/
def recordFerrers
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) :
    Ferrers.RecordFerrers P.endpointOddCount :=
  ⟨
    ⟨P.endpointIndexedCriticalProfile hp,
      P.endpointIndexedCriticalProfile_admissible hp⟩,
    hRecord
  ⟩

@[simp] theorem recordFerrers_profile_value
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) :
    (P.recordFerrers hp hRecord).profile.1 =
      P.endpointIndexedCriticalProfile hp :=
  rfl

/-- Record-compatible branch では width は少なくとも 2。 -/
theorem one_lt_endpointOddCount_of_recordCompatible
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) :
    1 < P.endpointOddCount := by
  unfold RecordCompatible Ferrers.IsRecordFerrersProfile at hRecord
  exact hRecord.1

/--
RecordFerrers branch では standard parity affine numerator `B` が既存の exact block fold

  B = 3^(p-1) + 2 * affineConstBlocks(canonicalLocalWords)

にそのまま一致する。
-/
theorem affineConst_eq_recordFactorization
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) :
    affineConst P.word =
      3 ^ (P.endpointOddCount - 1) +
        2 * Ferrers.affineConstBlocks
          (P.recordFerrers hp hRecord).canonicalLocalWords := by
  let R : Ferrers.RecordFerrers P.endpointOddCount :=
    P.recordFerrers hp hRecord
  have hProfile :
      Critical.profileAffineNumerator (P.endpointIndexedCriticalProfile hp) =
        affineConst P.word :=
    P.endpointIndexedCriticalProfile_affineNumerator_eq hp
  have hWord :
      Critical.profileAffineNumerator (P.endpointIndexedCriticalProfile hp) =
        Word.affineConst
          (Critical.wordOfProfile (P.endpointIndexedCriticalProfile hp)) :=
    Critical.profileAffineNumerator_eq_affineConst_wordOfProfile
      (P.endpointIndexedCriticalProfile_admissible hp) hp
  have hFactor := R.affineConst_wordOfProfile_eq_head_add_two_mul_blocks
  have hFactor' :
      Word.affineConst
          (Critical.wordOfProfile (P.endpointIndexedCriticalProfile hp)) =
        3 ^ (P.endpointOddCount - 1) +
          2 * Ferrers.affineConstBlocks R.canonicalLocalWords := by
    simpa [R, recordFerrers, Ferrers.RecordFerrers.profile] using hFactor
  calc
    affineConst P.word
        = Critical.profileAffineNumerator
            (P.endpointIndexedCriticalProfile hp) := hProfile.symm
    _ = Word.affineConst
          (Critical.wordOfProfile (P.endpointIndexedCriticalProfile hp)) := hWord
    _ = 3 ^ (P.endpointOddCount - 1) +
          2 * Ferrers.affineConstBlocks R.canonicalLocalWords := hFactor'
    _ = 3 ^ (P.endpointOddCount - 1) +
          2 * Ferrers.affineConstBlocks
            (P.recordFerrers hp hRecord).canonicalLocalWords := by
          rfl

end FirstPassagePath
end CSTMicro
end Collatz3
