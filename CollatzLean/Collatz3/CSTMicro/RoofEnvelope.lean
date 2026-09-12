import CollatzLean.Collatz3.CSTMicro.Compression
import CollatzLean.Collatz3.CSTMicro.Capacity
import CollatzLean.Collatz3.Core.PrefixAffine

/-!
# Collatz3 CSTMicro: Beatty roof による affine numerator の sharp envelope

critical first-passage exponent word では各 odd cut の prefix two-depth が
`beattyIndex k` 以下にある。

既存の exact prefix-sum formula

  B(w) = Σ 2^(prefixTwoDepth w k) * 3^(p-k-1)

の各 `prefixTwoDepth` を Beatty roof で上から置き換え、
word の細部に依存しない deterministic envelope

  B_roof(p) = Σ 2^(beattyIndex k) * 3^(p-k-1)

を定義する。

これは Stage 1 の粗い bound `B ≤ p * 3^(p-1)` をさらに sharpen する。
-/

namespace Collatz3
namespace CSTMicro

/-- `p` odd steps の roof envelope における第 `k` 項。 -/
def roofAffineTerm (p k : ℕ) : ℕ :=
  2 ^ Critical.beattyIndex k *
    3 ^ (p - (k + 1))

/--
critical first-passage で許される affine numerator の Beatty-roof envelope。

actual word の prefix depth を忘れ、critical roof だけを残した上界である。
-/
def roofAffineBound (p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range p, roofAffineTerm p k

@[simp] theorem roofAffineBound_zero :
    roofAffineBound 0 = 0 := by
  simp [roofAffineBound]

/--
critical exponent word の各 affine prefix term は対応する roof term 以下。
-/
theorem affinePrefixTerm_le_roofAffineTerm
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    Word.affinePrefixTerm w k ≤
      roofAffineTerm (Word.oddSteps w) k := by
  unfold Word.affinePrefixTerm roofAffineTerm
  have hDepth :
      Word.prefixTwoDepth w k ≤ Critical.beattyIndex k :=
    hFirst.prefixDepth_le_beatty hk
  have hPow :
      2 ^ Word.prefixTwoDepth w k ≤
        2 ^ Critical.beattyIndex k :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  exact Nat.mul_le_mul_right _ hPow

/--
critical exponent word の affine translation は `B_roof(p)` 以下。

新しい affine numerator を primitive にせず、既存 `Word.affineConst` の derived bound とする。
-/
theorem affineConst_le_roofAffineBound_of_critical
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w) :
    Word.affineConst w ≤ roofAffineBound (Word.oddSteps w) := by
  rw [← Word.affinePrefixNumerator_eq_affineConst w]
  unfold Word.affinePrefixNumerator roofAffineBound
  apply Finset.sum_le_sum
  intro k hk
  exact affinePrefixTerm_le_roofAffineTerm
    hFirst (Finset.mem_range.mp hk)

/--
一つの roof term は coarse envelope の一項 `3^(p-1)` 以下。
-/
theorem roofAffineTerm_le_threePow_pred
    {p k : ℕ}
    (hk : k < p) :
    roofAffineTerm p k ≤ 3 ^ (p - 1) := by
  unfold roofAffineTerm
  have hPow :
      2 ^ Critical.beattyIndex k ≤ 3 ^ k :=
    Critical.beattyIndex_lower k
  have hMul :
      2 ^ Critical.beattyIndex k * 3 ^ (p - (k + 1)) ≤
        3 ^ k * 3 ^ (p - (k + 1)) :=
    Nat.mul_le_mul_right _ hPow
  calc
    2 ^ Critical.beattyIndex k * 3 ^ (p - (k + 1))
        ≤ 3 ^ k * 3 ^ (p - (k + 1)) := hMul
    _ = 3 ^ (p - 1) := by
      have hExp : k + (p - (k + 1)) = p - 1 := by
        omega
      rw [← pow_add, hExp]

/--
roof envelope 自体は Stage 1 の coarse bound `p * 3^(p-1)` 以下。

したがって `B_roof` は単なる別表示ではなく、既存 coarse bound を refine する。
-/
theorem roofAffineBound_le_coarse (p : ℕ) :
    roofAffineBound p ≤ p * 3 ^ (p - 1) := by
  unfold roofAffineBound
  calc
    (∑ k ∈ Finset.range p, roofAffineTerm p k)
        ≤ ∑ k ∈ Finset.range p, 3 ^ (p - 1) := by
          apply Finset.sum_le_sum
          intro k hk
          exact roofAffineTerm_le_threePow_pred
            (Finset.mem_range.mp hk)
    _ = p * 3 ^ (p - 1) := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

namespace FirstPassagePath

/--
任意の standard first-passage path の affine numerator も endpoint odd count だけの
`B_roof` で抑えられる。

`p=0` の trivial even crossing は Stage 1 の coarse bound から直接処理し、
`p>0` では Stage 2B の exact compression を使う。
-/
theorem affineConst_le_roofAffineBound
    (P : FirstPassagePath) :
    affineConst P.word ≤ roofAffineBound P.endpointOddCount := by
  by_cases hp0 : P.endpointOddCount = 0
  · have hCoarse :=
      P.affineConst_le_endpointOddCount_mul_threePow_pred
    have hB0 : affineConst P.word = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hp0] using hCoarse
    rw [hB0, hp0]
    simp
  · have hp : 0 < P.endpointOddCount := Nat.pos_of_ne_zero hp0
    rcases P.exists_valid_critical_exponentWord hp with
      ⟨w, hValid, hCritical, hExpand⟩
    have hWordBound :=
      affineConst_le_roofAffineBound_of_critical hCritical
    have hB :
        affineConst P.word = Word.affineConst w := by
      calc
        affineConst P.word = affineConst (expandWord w) := by
          rw [hExpand]
        _ = Word.affineConst w :=
          affineConst_expandWord_eq_wordAffineConst hValid
    have hOdd :
        Word.oddSteps w = P.endpointOddCount := by
      calc
        Word.oddSteps w = oddCount (expandWord w) :=
          (oddCount_expandWord w).symm
        _ = oddCount P.word := by rw [hExpand]
        _ = P.endpointOddCount := rfl
    calc
      affineConst P.word = Word.affineConst w := hB
      _ ≤ roofAffineBound (Word.oddSteps w) := hWordBound
      _ = roofAffineBound P.endpointOddCount := by rw [hOdd]

/--
capacity 内の start は roof envelope による division-free cutoff も満たす。

  D * x ≤ B ≤ B_roof(p)
-/
theorem terminalGap_mul_start_le_roofAffineBound_of_withinCapacity
    {P : FirstPassagePath}
    {x : ℕ}
    (hCap : P.WithinCapacity x) :
    P.terminalGap * x ≤ roofAffineBound P.endpointOddCount := by
  exact le_trans hCap P.affineConst_le_roofAffineBound

/--
非下降する affine realization の start は roof envelope cutoff 内にある。
-/
theorem terminalGap_mul_start_le_roofAffineBound_of_nondecreasing
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hxy : x ≤ y) :
    P.terminalGap * x ≤ roofAffineBound P.endpointOddCount := by
  have hCap := P.withinCapacity_of_affine_start_le_end h hxy
  exact P.terminalGap_mul_start_le_roofAffineBound_of_withinCapacity hCap

/-- exact parity trace についての roof-envelope cutoff。 -/
theorem terminalGap_mul_start_le_roofAffineBound_of_nondecreasing_trace
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y) :
    P.terminalGap * x ≤ roofAffineBound P.endpointOddCount := by
  exact P.terminalGap_mul_start_le_roofAffineBound_of_nondecreasing
    h.affine hxy

end FirstPassagePath
end CSTMicro
end Collatz3
