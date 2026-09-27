import CollatzLean.Collatz3.CSTCarry.ProfileRowBridge
import CollatzLean.Collatz3.CSTMicro.FirstPassageArithmetic
import Mathlib.Data.List.TakeDrop

/-!
# Collatz3 CSTCarry: FirstPassagePath から CriticalCarryRows への bridge

`CSTMicro.FirstPassagePath` は standard parity word (`true=odd`, `false=even`) を使う一方、
`Critical.Profile` は odd-only exponent word の cumulative two-depth を使う。

このファイルでは両者の間に必要な最小の圧縮器を置く。

正の exponent `e` は standard parity block

  true, false, ..., false
        (合計 e step)

へ展開される。

逆に first-passage parity word を左から読み、各 odd step から次の odd step 直前までの
standard step 数を exponent として回収する。

その結果、positive endpoint odd count を持つ FirstPassagePath から得る exponent word は
`Critical.IsCriticalWord` を満たし、`profileOfWord` を経由して前ファイルの
`CriticalCarryRows` bridge へ exact に接続される。
-/

namespace Collatz3
namespace CSTMicro

open Critical
open CSTCarry

/-- odd-only exponent `e` を standard parity block へ展開する。 -/
def exponentParityBlock (e : ℕ) : ParityWord :=
  true :: List.replicate (e - 1) false

/-- exponent word 全体を standard parity word へ展開する。 -/
def expandExponentWord : Word → ParityWord
  | [] => []
  | e :: es => exponentParityBlock e ++ expandExponentWord es

@[simp] theorem expandExponentWord_nil :
    expandExponentWord ([] : Word) = [] := rfl

@[simp] theorem expandExponentWord_cons
    (e : ℕ) (es : Word) :
    expandExponentWord (e :: es) =
      exponentParityBlock e ++ expandExponentWord es := rfl

/-- exponent expansion は append を保存する。 -/
theorem expandExponentWord_append
    (u v : Word) :
    expandExponentWord (u ++ v) =
      expandExponentWord u ++ expandExponentWord v := by
  induction u with
  | nil => simp
  | cons e u ih =>
      simp [expandExponentWord, ih, List.append_assoc]

/-- parity odd count は append に加法的。 -/
theorem oddCount_append
    (u v : ParityWord) :
    oddCount (u ++ v) = oddCount u + oddCount v := by
  simp [oddCount, List.map_append]

/-- 一つの exponent block は odd step を exact に一つ持つ。 -/
@[simp] theorem oddCount_exponentParityBlock
    (e : ℕ) :
    oddCount (exponentParityBlock e) = 1 := by
  simp [exponentParityBlock, oddCount]

/-- valid exponent の standard block length は exponent 自身。 -/
theorem length_exponentParityBlock_of_pos
    {e : ℕ}
    (he : 0 < e) :
    (exponentParityBlock e).length = e := by
  simp [exponentParityBlock]
  omega

/-- expansion の odd count は exponent word length に一致する。 -/
theorem oddCount_expandExponentWord
    (w : Word) :
    oddCount (expandExponentWord w) = Word.oddSteps w := by
  induction w with
  | nil => simp [Word.oddSteps]
  | cons e w ih =>
      simp [expandExponentWord, oddCount_append, ih, Word.oddSteps]
      ring

/-- valid exponent word の expansion length は total two-depth に一致する。 -/
theorem length_expandExponentWord_of_valid
    {w : Word}
    (V : Word.Valid w) :
    (expandExponentWord w).length = Word.twoSteps w := by
  induction w with
  | nil => simp [Word.twoSteps]
  | cons e w ih =>
      have he : 0 < e := V e (by simp)
      have hTail : Word.Valid w := by
        intro a ha
        exact V a (by simp [ha])
      simp [expandExponentWord, length_exponentParityBlock_of_pos he,
        ih hTail, Word.twoSteps]

/-- valid word の proper odd prefix は total two-depth より strict に短い。 -/
theorem prefixTwoDepth_lt_twoSteps_of_valid
    {w : Word}
    (V : Word.Valid w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    Word.prefixTwoDepth w k < Word.twoSteps w := by
  induction w generalizing k with
  | nil =>
      simp [Word.oddSteps] at hk
  | cons e w ih =>
      have he : 0 < e := V e (by simp)
      have hTail : Word.Valid w := by
        intro a ha
        exact V a (by simp [ha])
      cases k with
      | zero =>
          simp [Word.prefixTwoDepth, Word.twoSteps, he]
      | succ k =>
          have hkTail : k < Word.oddSteps w := by
            simp only [Word.oddSteps_cons] at hk
            omega
          have hIH := ih hTail hkTail
          simpa [Nat.succ_eq_add_one] using Nat.add_lt_add_left hIH e

/--
expanded word を `k` odd blocks ちょうどの cumulative depth で切ると、
その prefix の odd count は exact に `k`。
-/
theorem prefixOddCount_expand_at_prefixTwoDepth
    {w : Word}
    (V : Word.Valid w)
    {k : ℕ}
    (hk : k ≤ Word.oddSteps w) :
    prefixOddCount (expandExponentWord w) (Word.prefixTwoDepth w k) = k := by
  have hValidTake : Word.Valid (w.take k) := by
    have hAll : Word.Valid (w.take k ++ w.drop k) := by
      rw [List.take_append_drop]
      exact V
    exact Word.Valid.prefix hAll
  have hSplit : w.take k ++ w.drop k = w :=
    List.take_append_drop k w
  have hExpandSplit :
      expandExponentWord w =
        expandExponentWord (w.take k) ++ expandExponentWord (w.drop k) := by
    rw [← expandExponentWord_append, hSplit]
  have hLength :
      (expandExponentWord (w.take k)).length = Word.prefixTwoDepth w k := by
    rw [length_expandExponentWord_of_valid hValidTake]
    rfl
  unfold prefixOddCount
  rw [hExpandSplit, ← hLength, List.take_left]
  rw [oddCount_expandExponentWord]
  have hkLen : k ≤ w.length := by
    simpa [Word.oddSteps] using hk
  simp [Word.oddSteps, hkLen]

/--
現在の odd block で既に `n>0` standard steps を消費している状態から、
残り parity word を exponent word へ圧縮する内部 decoder。
-/
def decodeParityTail : ParityWord → ℕ → Word
  | [], n => [n]
  | false :: v, n => decodeParityTail v (n + 1)
  | true :: v, n => n :: decodeParityTail v 1

/-- positive current block から始めれば decoder の全 exponent は正。 -/
theorem valid_decodeParityTail
    (v : ParityWord)
    {n : ℕ}
    (hn : 0 < n) :
    Word.Valid (decodeParityTail v n) := by
  induction v generalizing n with
  | nil =>
      simp [decodeParityTail, Word.Valid, hn]
  | cons b v ih =>
      cases b
      · exact ih (by omega)
      · simp only [decodeParityTail]
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hn
        · have hTail := ih (n := 1) (by omega)
          exact hTail e he

/-- positive block を false 一つ延長する exact identity。 -/
theorem exponentParityBlock_succ_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    exponentParityBlock (n + 1) = exponentParityBlock n ++ [false] := by
  cases n with
  | zero => omega
  | succ n =>
      simp [exponentParityBlock, List.replicate_succ']

/-- decoder は、既に消費した current block prefix と残り parity を exact に復元する。 -/
theorem expand_decodeParityTail
    (v : ParityWord)
    {n : ℕ}
    (hn : 0 < n) :
    exponentParityBlock n ++ v =
      expandExponentWord (decodeParityTail v n) := by
  induction v generalizing n with
  | nil =>
      simp [decodeParityTail, expandExponentWord]
  | cons b v ih =>
      cases b
      · simp only [decodeParityTail]
        rw [← ih (n := n + 1) (by omega)]
        rw [exponentParityBlock_succ_of_pos hn]
        simp [List.append_assoc]
      · simp only [decodeParityTail, expandExponentWord]
        rw [← ih (n := 1) (by omega)]
        simp [exponentParityBlock]

namespace FirstPassagePath

/-- positive endpoint odd count の first-passage path は odd branch から始まる。 -/
theorem exists_word_eq_true_cons
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    ∃ tail : ParityWord, P.word = true :: tail := by
  cases hWord : P.word with
  | nil =>
      simp [endpointOddCount, oddCount, hWord] at hp
  | cons b v =>
      cases b with
      | true =>
          exact ⟨v, rfl⟩
      | false =>
          have hv : v ≠ [] := by
            intro hvNil
            subst v
            simp [endpointOddCount, oddCount, hWord] at hp
          have hLen : 1 < P.length := by
            unfold length
            rw [hWord]
            simp only [List.length_cons]
            have : 0 < v.length := List.length_pos_iff.mpr hv
            omega
          have hExp := P.proper_expanding 1 (by omega) hLen
          unfold CoefficientExpandingAt at hExp
          rw [hWord] at hExp
          simp [prefixOddCount, oddCount] at hExp

/-- first-passage standard parity word を odd-only exponent word へ圧縮する。 -/
def exponentWord (P : FirstPassagePath) : Word :=
  match P.word with
  | true :: tail => decodeParityTail tail 1
  | _ => []

/-- positive endpoint odd count では exponent decoder が元 parity wordを exact に復元する。 -/
theorem expand_exponentWord_eq_word
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    expandExponentWord P.exponentWord = P.word := by
  rcases P.exists_word_eq_true_cons hp with ⟨tail, hWord⟩
  simp only [exponentWord]
  rw [hWord]
  have h := expand_decodeParityTail tail (n := 1) (by omega)
  simpa [exponentParityBlock] using h.symm

/-- positive endpoint odd count では圧縮 exponent word は valid。 -/
theorem exponentWord_valid
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.Valid P.exponentWord := by
  rcases P.exists_word_eq_true_cons hp with ⟨tail, hWord⟩
  simp only [exponentWord]
  rw [hWord]
  exact valid_decodeParityTail tail (by omega)

/-- 圧縮 exponent word の odd-step 数は path の endpoint odd count と一致。 -/
theorem exponentWord_oddSteps
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.oddSteps P.exponentWord = P.endpointOddCount := by
  have hExpand := P.expand_exponentWord_eq_word hp
  calc
    Word.oddSteps P.exponentWord
        = oddCount (expandExponentWord P.exponentWord) := by
            symm
            exact oddCount_expandExponentWord P.exponentWord
    _ = oddCount P.word := by rw [hExpand]
    _ = P.endpointOddCount := rfl

/-- 圧縮 exponent word の total depth は critical terminal depth と一致。 -/
theorem exponentWord_twoSteps
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.twoSteps P.exponentWord =
      criticalTwoDepth P.endpointOddCount := by
  have hValid := P.exponentWord_valid hp
  have hExpand := P.expand_exponentWord_eq_word hp
  calc
    Word.twoSteps P.exponentWord
        = (expandExponentWord P.exponentWord).length := by
            symm
            exact length_expandExponentWord_of_valid hValid
    _ = P.word.length := by rw [hExpand]
    _ = P.length := rfl
    _ = criticalTwoDepth P.endpointOddCount := P.length_eq_criticalTwoDepth

/--
first-passage proper odd-block prefix は Beatty critical roof 以下。
-/
theorem exponentWord_prefixTwoDepth_le_beatty
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    {k : ℕ}
    (hk : k < P.endpointOddCount) :
    Word.prefixTwoDepth P.exponentWord k ≤ beattyIndex k := by
  let w := P.exponentWord
  let t := Word.prefixTwoDepth w k
  have hValid : Word.Valid w := P.exponentWord_valid hp
  have hOdd : Word.oddSteps w = P.endpointOddCount := P.exponentWord_oddSteps hp
  have hkWord : k < Word.oddSteps w := by
    rw [hOdd]
    exact hk
  have htLtRaw := prefixTwoDepth_lt_twoSteps_of_valid hValid hkWord
  have hTwo : Word.twoSteps w = criticalTwoDepth P.endpointOddCount :=
    P.exponentWord_twoSteps hp
  have hLen : P.length = criticalTwoDepth P.endpointOddCount :=
    P.length_eq_criticalTwoDepth
  have htLt : t < P.length := by
    dsimp [t]
    rw [hTwo] at htLtRaw
    rw [hLen]
    exact htLtRaw
  have hCountExpand :=
    prefixOddCount_expand_at_prefixTwoDepth hValid (Nat.le_of_lt hkWord)
  have hExpand := P.expand_exponentWord_eq_word hp
  have hCount : prefixOddCount P.word t = k := by
    dsimp [t] at hCountExpand ⊢
    rw [← hExpand]
    exact hCountExpand
  by_cases hk0 : k = 0
  · simp [hk0, Word.prefixTwoDepth]
  have htPos : 0 < t := by
    by_contra hNot
    have htZero : t = 0 := by omega
    rw [htZero] at hCount
    simp only [prefixOddCount_zero] at hCount
    omega
  have hExp := P.proper_expanding t htPos htLt
  unfold CoefficientExpandingAt at hExp
  rw [hCount] at hExp
  by_contra hNotLe
  have hNotLe' : ¬ t ≤ beattyIndex k := by
    simpa [t, w] using hNotLe
  have hBeattyLt : beattyIndex k < t :=
  Nat.lt_of_not_ge hNotLe'
  have hExpLe : beattyIndex k + 1 ≤ t := by omega
  have hPowLe : 2 ^ (beattyIndex k + 1) ≤ 2 ^ t :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExpLe
  have hUpper := beattyIndex_upper k
  have hBad : 2 ^ t < 2 ^ t := by
    calc
      2 ^ t < 3 ^ k := hExp
      _ ≤ 2 ^ (beattyIndex k + 1) := hUpper
      _ ≤ 2 ^ t := hPowLe
  omega

/--
## FirstPassagePath -> IsCriticalWord bridge

positive endpoint odd count を持つ standard first-passage path を odd-only に圧縮すると、
その exponent word は genuine critical word shape になる。
-/
theorem exponentWord_isCriticalWord
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    IsCriticalWord P.endpointOddCount P.exponentWord := by
  refine ⟨P.exponentWord_valid hp,
    P.exponentWord_oddSteps hp,
    P.exponentWord_twoSteps hp,
    ?_⟩
  intro k hk
  exact P.exponentWord_prefixTwoDepth_le_beatty hp hk

/-- FirstPassagePath から profile を経由して canonical carry rows を作る。 -/
def carryRows (P : FirstPassagePath) : List FerrersRow :=
  profileCarryRows
    (profileOfWord (m := P.endpointOddCount) P.exponentWord)

@[simp] theorem carryRows_length
    (P : FirstPassagePath) :
    P.carryRows.length = P.endpointOddCount := by
  simp [carryRows]

/--
## FirstPassagePath -> CriticalCarryRows bridge

これが FirstPassagePath 側の中心結論。
positive endpoint odd count の first-passage path から canonical に作った rows は
`CriticalCarryRows` を満たす。
-/
theorem carryRows_critical
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    CriticalCarryRows P.endpointOddCount P.carryRows := by
  have C := P.exponentWord_isCriticalWord hp
  exact criticalCarryRows_profileCarryRows (admissible_profileOfWord C)

/--
`2 <= p <= 26` なら、FirstPassagePath 由来の canonical rows に対する carry recurrence は
final wrap で終われない。

前段の `CriticalCarryRows` 仮定を、今回の bridge により path geometry から除去した形。
-/
theorem final_lt_modulus_of_carryRows_le_26
    (P : FirstPassagePath)
    {digits : List ℕ}
    {F : ℕ}
    (hCarry : CarryRealizes
      (2 ^ criticalTwoDepth P.endpointOddCount)
      P.carryRows 0 digits F)
    (hp2 : 2 ≤ P.endpointOddCount)
    (hp26 : P.endpointOddCount ≤ 26) :
    F < 2 ^ criticalTwoDepth P.endpointOddCount := by
  exact hCarry.final_lt_modulus_of_criticalRows_le_26
    (P.carryRows_critical (by omega)) hp2 hp26

end FirstPassagePath

end CSTMicro
end Collatz3
