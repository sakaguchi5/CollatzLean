import CollatzLean.Collatz3.CSTMicro.AffineExpansion
import CollatzLean.Collatz3.CSTMicro.FirstPassageArithmetic
import CollatzLean.Collatz3.Critical.FirstPassage

/-!
# Collatz3 CSTMicro: standard first passage と critical exponent word の一致

valid odd-only exponent word `w` を standard parity word `expandWord w` へ展開すると、
`Word.CriticalFirstPassage w` は standard `FirstPassagePath` を与える。

逆に、ある standard first-passage path の word が `expandWord w` なら、
`w` は `Word.CriticalFirstPassage` を満たす。

これにより standard coefficient stopping time と既存 Collatz3 critical word geometry を、
同じ first crossing の二つの座標表示として接続する。
-/

namespace Collatz3
namespace CSTMicro

/-- valid critical exponent word から standard first-passage path を構成する。 -/
def firstPassagePathOfCritical
    (w : Word)
    (hValid : Word.Valid w)
    (hFirst : Word.CriticalFirstPassage w) :
    FirstPassagePath where
  word := expandWord w
  nonempty := by
    intro hNil
    have hLenZero := congrArg List.length hNil
    have hLen := length_expandWord_of_valid hValid
    have hTwoPos : 0 < Word.twoSteps w := by
      rw [hFirst.totalTwoDepth_eq]
      simp [Critical.criticalTwoDepth]
    rw [hLen] at hLenZero
    simp at hLenZero
    omega
  proper_expanding := by
    intro k hkPos hkLt
    unfold CoefficientExpandingAt
    have hLen := length_expandWord_of_valid hValid
    have hkTotal : k < Word.prefixTwoDepth w (Word.oddSteps w) := by
      rw [Word.prefixTwoDepth_oddSteps]
      simpa [hLen] using hkLt
    have hex : ∃ j : ℕ, k < Word.prefixTwoDepth w j :=
      ⟨Word.oddSteps w, hkTotal⟩
    let j : ℕ := Nat.find hex
    have hjSpec : k < Word.prefixTwoDepth w j := by
      dsimp [j]
      exact Nat.find_spec hex
    have hjLe : j ≤ Word.oddSteps w := by
      dsimp [j]
      exact Nat.find_min' hex hkTotal
    have hjPos : 0 < j := by
      by_contra hNot
      have hj0 : j = 0 := by omega
      rw [hj0] at hjSpec
      simp at hjSpec
    let i : ℕ := j - 1
    have hij : i + 1 = j := by
      dsimp [i]
      omega
    have hiLtJ : i < j := by omega
    have hNotBefore : ¬ k < Word.prefixTwoDepth w i := by
      apply Nat.find_min hex
      simpa [j] using hiLtJ
    have hSiLeK : Word.prefixTwoDepth w i ≤ k :=
      Nat.le_of_not_gt hNotBefore
    have hiLtP : i < Word.oddSteps w := by omega
    have hCountAtI :=
      prefixOddCount_expandWord_prefixTwoDepth hValid (j := i) (by omega)
    have hiCount :
        i ≤ prefixOddCount (expandWord w) k := by
      calc
        i = prefixOddCount (expandWord w) (Word.prefixTwoDepth w i) :=
          hCountAtI.symm
        _ ≤ prefixOddCount (expandWord w) k :=
          prefixOddCount_mono _ hSiLeK
    by_cases hkEq : k = Word.prefixTwoDepth w i
    · have hiPos : 0 < i := by
        by_contra hNot
        have hi0 : i = 0 := by omega
        rw [hi0] at hkEq
        simp at hkEq
        omega
      have hCut := hFirst.properCut_twoPow_lt_threePow hiPos hiLtP
      have hThree :
          3 ^ i ≤ 3 ^ prefixOddCount (expandWord w) k :=
        Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hiCount
      rw [hkEq] at hThree
      rw [hkEq]
      exact lt_of_lt_of_le hCut hThree
    · have hSiLtK : Word.prefixTwoDepth w i < k := by omega
      have hSuccLe : Word.prefixTwoDepth w i + 1 ≤ k := by omega
      have hCountSucc :=
        prefixOddCount_expandWord_succ_prefixTwoDepth hValid hiLtP
      have hjCount :
          j ≤ prefixOddCount (expandWord w) k := by
        calc
          j = i + 1 := hij.symm
          _ = prefixOddCount (expandWord w)
                (Word.prefixTwoDepth w i + 1) := hCountSucc.symm
          _ ≤ prefixOddCount (expandWord w) k :=
                prefixOddCount_mono _ hSuccLe
      have hTwoThree : 2 ^ k < 3 ^ j := by
        by_cases hjLtP : j < Word.oddSteps w
        · have hCut :=
            hFirst.properCut_twoPow_lt_threePow hjPos hjLtP
          have hkLe : k ≤ Word.prefixTwoDepth w j := le_of_lt hjSpec
          have hPowLe :
              2 ^ k ≤ 2 ^ Word.prefixTwoDepth w j :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hkLe
          exact lt_of_le_of_lt hPowLe hCut
        · have hjEq : j = Word.oddSteps w := by omega
          rw [hjEq] at hjSpec ⊢
          rw [Word.prefixTwoDepth_oddSteps, hFirst.totalTwoDepth_eq] at hjSpec
          have hkBeatty : k ≤ Critical.beattyIndex (Word.oddSteps w) := by
            simp [Critical.criticalTwoDepth] at hjSpec
            omega
          have hPowLe :
              2 ^ k ≤ 2 ^ Critical.beattyIndex (Word.oddSteps w) :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hkBeatty
          have hpPos : 0 < Word.oddSteps w := hFirst.oddSteps_pos
          exact lt_of_le_of_lt hPowLe
            (Critical.beattyIndex_lower_strict hpPos)
      have hThree :
          3 ^ j ≤ 3 ^ prefixOddCount (expandWord w) k :=
        Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hjCount
      exact lt_of_lt_of_le hTwoThree hThree
  terminal_contracting := by
    have hTerm := hFirst.terminal_threePow_lt_twoPow
    unfold CoefficientContracting
    rw [oddCount_expandWord]
    rw [length_expandWord_of_valid hValid]
    exact hTerm

@[simp] theorem firstPassagePathOfCritical_word
    (w : Word)
    (hValid : Word.Valid w)
    (hFirst : Word.CriticalFirstPassage w) :
    (firstPassagePathOfCritical w hValid hFirst).word = expandWord w := rfl

/-- expanded word が standard first-passage path なら元 exponent word は critical first-passage。 -/
theorem criticalFirstPassage_of_expanded_firstPassage
    {w : Word}
    (hValid : Word.Valid w)
    (P : FirstPassagePath)
    (hWord : P.word = expandWord w) :
    Word.CriticalFirstPassage w := by
  have hLen : P.length = Word.twoSteps w := by
    calc
      P.length = P.word.length := rfl
      _ = (expandWord w).length := by rw [hWord]
      _ = Word.twoSteps w := length_expandWord_of_valid hValid
  have hOdd : P.endpointOddCount = Word.oddSteps w := by
    calc
      P.endpointOddCount = oddCount P.word := rfl
      _ = oddCount (expandWord w) := by rw [hWord]
      _ = Word.oddSteps w := oddCount_expandWord w
  constructor
  · have hCritical := P.length_eq_criticalTwoDepth
    rw [hLen, hOdd] at hCritical
    exact hCritical
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
    · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
      let k := Word.prefixTwoDepth w j
      have hkPos : 0 < k :=
        Word.prefixTwoDepth_pos_of_valid hValid hjPos (by omega)
      have hkLtTotal : k < Word.twoSteps w :=
        Word.prefixTwoDepth_lt_twoSteps_of_valid hValid hj
      have hkLt : k < P.length := by
        rw [hLen]
        exact hkLtTotal
      have hExp := P.proper_expanding k hkPos hkLt
      unfold CoefficientExpandingAt at hExp
      have hCount :=
        prefixOddCount_expandWord_prefixTwoDepth hValid
          (j := j) (by omega)
      have hCountP : prefixOddCount P.word k = j := by
        dsimp [k]
        rw [hWord]
        exact hCount
      rw [hCountP] at hExp
      by_contra hNot
      have hBeattyLt : Critical.beattyIndex j < Word.prefixTwoDepth w j := by
        omega
      have hSuccLe :
          Critical.beattyIndex j + 1 ≤ Word.prefixTwoDepth w j := by
        omega
      have hUpper := Critical.beattyIndex_upper j
      have hPowLe :
          2 ^ (Critical.beattyIndex j + 1) ≤
            2 ^ Word.prefixTwoDepth w j :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hSuccLe
      have hContra : 3 ^ j ≤ 2 ^ Word.prefixTwoDepth w j :=
        le_trans hUpper hPowLe
      dsimp [k] at hExp
      omega

/--
valid exponent wordについて、expanded standard first-passage path の存在と
`Word.CriticalFirstPassage` は同値。
-/
theorem exists_expanded_firstPassagePath_iff_critical
    {w : Word}
    (hValid : Word.Valid w) :
    (∃ P : FirstPassagePath, P.word = expandWord w) ↔
      Word.CriticalFirstPassage w := by
  constructor
  · rintro ⟨P, hP⟩
    exact criticalFirstPassage_of_expanded_firstPassage hValid P hP
  · intro hFirst
    exact ⟨firstPassagePathOfCritical w hValid hFirst, rfl⟩

end CSTMicro
end Collatz3
