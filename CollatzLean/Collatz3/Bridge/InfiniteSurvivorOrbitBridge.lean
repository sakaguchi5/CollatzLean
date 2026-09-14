import CollatzLean.Collatz3.Bridge.NaturalSurvivorResidueStability
import CollatzLean.Collatz3.Bridge.SurvivorActualResidue
import CollatzLean.Collatz3.Semantics.OddOrbit

/-!
# Collatz3 Bridge: actual OddOrbit と infinite coefficient survivor

`InfiniteSurvivorDefect` では無限 exponent stream を pure data として扱った。
このファイルでは actual `OddOrbit` の exponent stream をそこへ接続する。

設計上の注意:

* actual odd-only orbit の finite prefix は `OddOrbit.segmentWord` を正本にする。
* physical parity tree 全体を新しい無限 structure として複製しない。
* odd-block endpoint `m` では total physical depth

    `D_m = exponent 0 + ... + exponent (m-1)`

  の survivor composition を actual segment word から直接作る。
* その residue は実際の初期値 `O.value 0 mod 2^D_m` と exact に一致する。

従って defect stream、finite survivor code、actual 2進 residue が同じ軌道の
同じ有限 prefix を表すことが明示される。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/-- actual odd-only orbit が全 odd-block endpoint で coefficient expansion 側に残る。 -/
def IsInfiniteCoefficientSurvivor (O : Collatz3.OddOrbit) : Prop :=
  IsInfiniteSurvivorExponentStream O.exponent

namespace IsInfiniteCoefficientSurvivor

/-- actual survivor orbit の exponent は各 step で正。 -/
theorem exponent_pos
    {O : Collatz3.OddOrbit}
    (S : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    0 < O.exponent m :=
  Bridge.IsInfiniteSurvivorExponentStream.exponent_pos S m

/-- actual survivor orbit の累積 two-depth は Beatty roof 以下。 -/
theorem prefixDepth_le_beatty
    {O : Collatz3.OddOrbit}
    (S : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    infinitePrefixDepth O.exponent m ≤ Critical.beattyIndex m :=
  Bridge.IsInfiniteSurvivorExponentStream.prefixDepth_le_beatty S m

end IsInfiniteCoefficientSurvivor

/-- segment word は隣接区間の連結に exact に一致する。 -/
theorem segmentWord_add
    (O : Collatz3.OddOrbit)
    (i q r : ℕ) :
    O.segmentWord i (q + r) =
      O.segmentWord i q ++ O.segmentWord (i + q) r := by
  induction q generalizing i with
  | zero =>
      simp
  | succ q ih =>
      rw [Nat.succ_add]
      simp only [Collatz3.OddOrbit.segmentWord_succ]
      rw [ih (i + 1)]
      simp [Nat.add_assoc]
      ring_nf

/--
実軌道の先頭 `m` odd steps の total two-depth は pure infinite prefix depth と一致する。
-/
theorem twoSteps_segmentWord_zero_eq_infinitePrefixDepth
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    Word.twoSteps (O.segmentWord 0 m) =
      infinitePrefixDepth O.exponent m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hSplit := O.segmentWord_add 0 m 1
      rw [show m + 1 = Nat.succ m by omega] at hSplit
      rw [hSplit, Word.twoSteps_append, ih]
      simp [Collatz3.OddOrbit.segmentWord]

/--
任意 start `a` から `r` odd steps の two-depth は global prefix depth の増分。
-/
theorem infinitePrefixDepth_add_eq
    (O : Collatz3.OddOrbit)
    (a r : ℕ) :
    infinitePrefixDepth O.exponent (a + r) =
      infinitePrefixDepth O.exponent a +
        Word.twoSteps (O.segmentWord a r) := by
  have hSplit := O.segmentWord_add 0 a r
  have hAll := O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth (a + r)
  have hHead := O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth a
  rw [hSplit, Word.twoSteps_append, hHead] at hAll
  simpa using hAll.symm

/-- `k ≤ q` なら segment word の先頭 `k` steps は shorter segment そのもの。 -/
theorem segmentWord_take
    (O : Collatz3.OddOrbit)
    (i q k : ℕ)
    (hk : k ≤ q) :
    (O.segmentWord i q).take k = O.segmentWord i k := by
  have hq : q = k + (q - k) := by
    omega
  rw [hq, O.segmentWord_add]
  have hLen : (O.segmentWord i k).length = k := by
    simpa [Word.oddSteps] using O.segmentWord_oddSteps i k
  rw [List.take_append_of_le_length]
  · simpa only [hLen] using
      (List.take_length (l := O.segmentWord i k))
  · rw [hLen]

/-- actual segment の prefix two-depth は shorter actual segment の total depth。 -/
theorem prefixTwoDepth_segmentWord
    (O : Collatz3.OddOrbit)
    (i q k : ℕ)
    (hk : k ≤ q) :
    Word.prefixTwoDepth (O.segmentWord i q) k =
      Word.twoSteps (O.segmentWord i k) := by
  unfold Word.prefixTwoDepth
  rw [O.segmentWord_take i q k hk]

/-- positive exponent stream では prefix block 数以上の two-depth を持つ。 -/
theorem index_le_infinitePrefixDepth
    {O : Collatz3.OddOrbit}
    (S : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    m ≤ infinitePrefixDepth O.exponent m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [infinitePrefixDepth_succ]
      have he := IsInfiniteCoefficientSurvivor.exponent_pos S m
      omega

/-- positive odd-block endpoint では physical depth も正。 -/
theorem infinitePrefixDepth_pos
    {O : Collatz3.OddOrbit}
    (S : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    0 < infinitePrefixDepth O.exponent m := by
  exact lt_of_lt_of_le hm (index_le_infinitePrefixDepth S m)

/--
actual first `m` odd steps を、その total physical depth の parity composition として束ねる。
-/
def endpointParityComposition
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    ParityComposition (infinitePrefixDepth O.exponent m) :=
  validExponentWordEquivParityComposition
    (infinitePrefixDepth O.exponent m)
    ⟨O.segmentWord 0 m,
      O.segmentWord_valid 0 m,
      O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth m⟩

@[simp] theorem endpointParityComposition_blocks
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    (O.endpointParityComposition m).blocks = O.segmentWord 0 m :=
  rfl

@[simp] theorem endpointParityComposition_length
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    (O.endpointParityComposition m).length = m := by
  change Word.oddSteps (O.segmentWord 0 m) = m
  simp

/-- endpoint composition の block-prefix size は global survivor depth。 -/
theorem endpointParityComposition_sizeUpTo
    (O : Collatz3.OddOrbit)
    (m k : ℕ)
    (hk : k ≤ m) :
    (O.endpointParityComposition m).sizeUpTo k =
      infinitePrefixDepth O.exponent k := by
  change Word.prefixTwoDepth (O.segmentWord 0 m) k = _
  rw [O.prefixTwoDepth_segmentWord 0 m k hk]
  exact O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth k

/--
actual infinite survivor の odd-block endpoint は finite `SurvivorParityCode` を与える。
-/
def endpointSurvivorCode
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    SurvivorParityCode (infinitePrefixDepth O.exponent m) := by
  let c := O.endpointParityComposition m
  refine ⟨c, ?_⟩
  constructor
  · have hDepth := S.prefixDepth_le_beatty m
    have hPow :
        2 ^ infinitePrefixDepth O.exponent m ≤
          2 ^ Critical.beattyIndex m :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
    have hRoof := Critical.beattyIndex_lower m
    simpa [c, O.endpointParityComposition_length m] using
      (le_trans hPow hRoof)
  · intro k hk
    have hkm : k < m := by
      simpa [c, O.endpointParityComposition_length m] using hk
    have hDepth := S.prefixDepth_le_beatty k
    have hPow :
        2 ^ infinitePrefixDepth O.exponent k ≤
          2 ^ Critical.beattyIndex k :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
    have hRoof := Critical.beattyIndex_lower k
    have hSize := O.endpointParityComposition_sizeUpTo m k (Nat.le_of_lt hkm)
    change 2 ^ c.sizeUpTo k ≤ 3 ^ k
    rw [show c.sizeUpTo k = infinitePrefixDepth O.exponent k by
      simpa [c] using hSize]
    exact le_trans hPow hRoof

@[simp] theorem endpointSurvivorCode_length
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    (O.endpointSurvivorCode S m).1.length = m := by
  change (O.endpointParityComposition m).length = m
  exact O.endpointParityComposition_length m

/-- endpoint survivor code の prefix size は infinite survivor depth そのもの。 -/
theorem endpointSurvivorCode_sizeUpTo
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (m k : ℕ)
    (hk : k ≤ m) :
    (O.endpointSurvivorCode S m).1.sizeUpTo k =
      infinitePrefixDepth O.exponent k := by
  change (O.endpointParityComposition m).sizeUpTo k = _
  exact O.endpointParityComposition_sizeUpTo m k hk

/--
actual endpoint survivor code が持つ residue は、実際の orbit start `O.value 0` の
`2^D_m` 剰余と exact に一致する。
-/
theorem endpointSurvivorResidue_eq_start_mod
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    (parityCompositionResidue
        (infinitePrefixDepth_pos S hm)
        (O.endpointSurvivorCode S m).1).1 =
      O.value 0 % 2 ^ infinitePrefixDepth O.exponent m := by
  let w := O.segmentWord 0 m
  let D := infinitePrefixDepth O.exponent m
  have hD : Word.twoSteps w = D := by
    simpa [w, D] using O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth m
  have hne : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps 0 m
    change Word.oddSteps w = m at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hRun : Runs w (O.value 0) (O.value m) := by
    simpa [w] using O.runsSegment 0 m
  rcases hRun.exists_canonicalLift hne with ⟨k, hx, _hy⟩
  rw [parityCompositionResidue_val]
  change Word.canonicalStart w % 2 ^ D = O.value 0 % 2 ^ D
  have hPeriod :
      Word.oddEndpointModulus w * k = 2 ^ D * (2 * k) := by
    rw [Word.oddEndpointModulus_eq, hD, pow_succ]
    ring
  rw [hx, hPeriod, Nat.add_mul_mod_self_left]

/-- actual survivor start は各 odd-block endpoint depth の survivor residue union に属する。 -/
theorem isSurvivorResidueStart_at_endpoint
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    IsSurvivorResidueStart
      (infinitePrefixDepth O.exponent m)
      (infinitePrefixDepth_pos S hm)
      (O.value 0) := by
  refine ⟨O.endpointSurvivorCode S m, ?_⟩
  exact (O.endpointSurvivorResidue_eq_start_mod S hm).symm

end OddOrbit
end Collatz3
