import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselPrimitiveZeroClosure

/-!
# Restarted suffix Hensel: width >= 37 の最終 closure

nonzero repeated-block branch は `RestartedSuffixHenselNonzeroRepeat` で既に排除済み。
従って `width >= 37` では maximal half-width repeat は zero scaled-difference になる。

本ファイルでは

1. zero repeat を gcd で primitive period `(d,e)` へ圧縮し、
2. `sameDeltaOffsetBlock_extend_divisor` でその短周期を元の half-width block 全体へ延長し、
3. primitive cycle を `(d,e)=(1,0)` または `(2,1)` に分類し、
4. 12 cell の Beatty displacement がそれぞれ `12` または `18` になることを示し、
5. `beattyIndex 12 = 19` と Beatty additivity (`19` または `20`) に矛盾させる。

これにより actual restarted packet の `width >= 37` branch は axiom なしで閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- `beattyIndex 12 = 19`。実数 log を使わず power inequality だけで確認する。 -/
private theorem beattyIndex_twelve_eq_nineteen :
    beattyIndex 12 = 19 := by
  apply Nat.le_antisymm
  · apply beattyIndex_le_of_upper
    norm_num
  · by_contra hnot
    have hle : beattyIndex 12 ≤ 18 := by omega
    have hUpper := beattyIndex_upper 12
    have hExp : beattyIndex 12 + 1 ≤ 19 := by omega
    have hPowLe :
        2 ^ (beattyIndex 12 + 1) ≤ (2 : ℕ) ^ 19 :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp
    have hBad : (3 : ℕ) ^ 12 ≤ 2 ^ 19 :=
      le_trans hUpper hPowLe
    norm_num at hBad

namespace MonotoneSuffixHenselChain

/-- period `1`, offset `0` が12 cell 続けば `delta_(i+12)=delta_i`。 -/
private theorem delta_add_twelve_eq_of_period_one_zero
    (C : MonotoneSuffixHenselChain)
    {i m : ℕ}
    (hm : 12 ≤ m)
    (hBlock : C.SameDeltaOffsetBlock i (i + 1) m 0) :
    C.delta (i + 12) = C.delta i := by
  have h0 : C.delta (i + 1) = C.delta i := by
    simpa using hBlock 0 (by omega)
  have h1 : C.delta (i + 2) = C.delta (i + 1) := by
    simpa [Nat.add_assoc] using hBlock 1 (by omega)
  have h2 : C.delta (i + 3) = C.delta (i + 2) := by
    simpa [Nat.add_assoc] using hBlock 2 (by omega)
  have h3 : C.delta (i + 4) = C.delta (i + 3) := by
    simpa [Nat.add_assoc] using hBlock 3 (by omega)
  have h4 : C.delta (i + 5) = C.delta (i + 4) := by
    simpa [Nat.add_assoc] using hBlock 4 (by omega)
  have h5 : C.delta (i + 6) = C.delta (i + 5) := by
    simpa [Nat.add_assoc] using hBlock 5 (by omega)
  have h6 : C.delta (i + 7) = C.delta (i + 6) := by
    simpa [Nat.add_assoc] using hBlock 6 (by omega)
  have h7 : C.delta (i + 8) = C.delta (i + 7) := by
    simpa [Nat.add_assoc] using hBlock 7 (by omega)
  have h8 : C.delta (i + 9) = C.delta (i + 8) := by
    simpa [Nat.add_assoc] using hBlock 8 (by omega)
  have h9 : C.delta (i + 10) = C.delta (i + 9) := by
    simpa [Nat.add_assoc] using hBlock 9 (by omega)
  have h10 : C.delta (i + 11) = C.delta (i + 10) := by
    simpa [Nat.add_assoc] using hBlock 10 (by omega)
  have h11 : C.delta (i + 12) = C.delta (i + 11) := by
    simpa [Nat.add_assoc] using hBlock 11 (by omega)
  omega

/-- period `2`, offset `1` が12 cell 続けば `delta_(i+12)=delta_i+6`。 -/
private theorem delta_add_twelve_eq_add_six_of_period_two_one
    (C : MonotoneSuffixHenselChain)
    {i m : ℕ}
    (hm : 12 ≤ m)
    (hBlock : C.SameDeltaOffsetBlock i (i + 2) m 1) :
    C.delta (i + 12) = C.delta i + 6 := by
  have h0 : C.delta (i + 2) = C.delta i + 1 := by
    simpa using hBlock 0 (by omega)
  have h2 : C.delta (i + 4) = C.delta (i + 2) + 1 := by
    simpa [Nat.add_assoc] using hBlock 2 (by omega)
  have h4 : C.delta (i + 6) = C.delta (i + 4) + 1 := by
    simpa [Nat.add_assoc] using hBlock 4 (by omega)
  have h6 : C.delta (i + 8) = C.delta (i + 6) + 1 := by
    simpa [Nat.add_assoc] using hBlock 6 (by omega)
  have h8 : C.delta (i + 10) = C.delta (i + 8) + 1 := by
    simpa [Nat.add_assoc] using hBlock 8 (by omega)
  have h10 : C.delta (i + 12) = C.delta (i + 10) + 1 := by
    simpa [Nat.add_assoc] using hBlock 10 (by omega)
  omega

end MonotoneSuffixHenselChain

namespace RestartedTerminalStraightPacket

/--
period `(1,0)` が half-width block 全体へ延長されている場合、
12-cell Beatty displacement は `12` になり `beattyIndex 12 = 19` と矛盾する。
-/
private theorem false_of_extended_period_one_zero
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i m : ℕ}
    (hm : 12 ≤ m)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + 1) m 0) :
    False := by
  dsimp at hBlock
  let C := S.toMonotoneSuffixHenselChain hStart
  have hDeltaC :=
    MonotoneSuffixHenselChain.delta_add_twelve_eq_of_period_one_zero C hm hBlock
  have hDelta :
      S.suffixHenselDelta (i + 12) =
        S.suffixHenselDelta i := by
    dsimp [C, toMonotoneSuffixHenselChain] at hDeltaC
    exact hDeltaC
  have hRel := S.suffixHenselDelta_relative_exact i 12
  rw [hDelta] at hRel
  have hDisp :
      beattyIndex (S.b + i + 12) - beattyIndex (S.b + i) = 12 := by
    omega
  have hAdd := beattyIndex_add_eq_add_or_add_one (S.b + i) 12
  rw [beattyIndex_twelve_eq_nineteen] at hAdd
  rcases hAdd with hNoCarry | hCarry
  · omega
  · omega

/--
period `(2,1)` が half-width block 全体へ延長されている場合、
12-cell Beatty displacement は `18` になり `beattyIndex 12 = 19` と矛盾する。
-/
private theorem false_of_extended_period_two_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i m : ℕ}
    (hm : 12 ≤ m)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + 2) m 1) :
    False := by
  dsimp at hBlock
  let C := S.toMonotoneSuffixHenselChain hStart
  have hDeltaC :=
    MonotoneSuffixHenselChain.delta_add_twelve_eq_add_six_of_period_two_one C hm hBlock
  have hDelta :
      S.suffixHenselDelta (i + 12) =
        S.suffixHenselDelta i + 6 := by
    dsimp [C, toMonotoneSuffixHenselChain] at hDeltaC
    exact hDeltaC
  have hRel := S.suffixHenselDelta_relative_exact i 12
  rw [hDelta] at hRel
  have hDisp :
      beattyIndex (S.b + i + 12) - beattyIndex (S.b + i) = 18 := by
    omega
  have hAdd := beattyIndex_add_eq_add_or_add_one (S.b + i) 12
  rw [beattyIndex_twelve_eq_nineteen] at hAdd
  rcases hAdd with hNoCarry | hCarry
  · omega
  · omega

/--
`width >= 37` の actual restarted suffix-Hensel branch は存在しない。

nonzero repeat は既存 size theorem で zero に強制される。
zero repeat は gcd primitive reduction + divisor-period extension により
`(1,0)` または `(2,1)` の12-cell pattern を作り、Beatty arithmetic と矛盾する。
-/
theorem restartedSuffixHensel_false_of_width_ge_37
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : 37 ≤ S.width) :
    False := by
  let C := S.toMonotoneSuffixHenselChain hStart
  let m := (S.width - 1) / 2
  have hm : 12 ≤ m := by
    dsimp [m]
    omega
  rcases
      S.exists_forced_zero_scaledDifference_of_width_ge_37
        hStart hWidth with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, hZero⟩
  let p := j - i
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hip : i + p = j := by
    dsimp [p]
    omega
  have hpPred : p - 1 ≤ m := by
    dsimp [p]
    omega
  have hjEndS : j + m ≤ S.width := by
    dsimp [C, toMonotoneSuffixHenselChain] at hjEnd
    simpa [m] using hjEnd
  have hEnd : i + p + m ≤ S.width := by
    rw [hip]
    exact hjEndS
  have hBlockP : C.SameDeltaOffsetBlock i (i + p) m Delta := by
    rw [hip]
    exact hBlock
  have hZeroP : C.scaledDifference i (i + p) Delta 0 = 0 := by
    rw [hip]
    exact hZero
  rcases
      S.zeroRepeat_exists_primitiveCycle
        hStart hp hpPred hEnd hBlockP hZeroP with
    ⟨d, e, hd, hdLe, hCoprime, hState, hPrimitiveBlock, hRise⟩
  have hRoom : i + (2 * d - 1) ≤ S.width := by
    omega
  have hCases :=
    S.primitiveZeroCycle_period_offset_cases
      hStart hd hCoprime hRoom hState hRise
  rcases hCases with hOne | hTwo
  · rcases hOne with ⟨hdOne, heZero⟩
    subst d
    subst e
    exact
      S.false_of_extended_period_one_zero
        hStart hm hPrimitiveBlock
  · rcases hTwo with ⟨hdTwo, heOne⟩
    subst d
    subst e
    exact
      S.false_of_extended_period_two_one
        hStart hm hPrimitiveBlock

/-- large-width closure の読みやすい corollary。 -/
theorem restartedSuffixHensel_width_lt_37
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    S.width < 37 := by
  by_contra hnot
  have hWidth : 37 ≤ S.width := by omega
  exact S.restartedSuffixHensel_false_of_width_ge_37 hStart hWidth

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
