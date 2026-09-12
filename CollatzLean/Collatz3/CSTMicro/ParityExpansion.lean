import CollatzLean.Collatz3.CSTMicro.Affine
import CollatzLean.Collatz3.Core.PrefixDepth
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTMicro: exponent word の standard parity 展開

odd-only exponent `e` 一文字を

  true :: false^(e-1)

へ展開する。valid word では各 exponent が正なので、この block の standard length は exact に `e`。

このファイルでは pure list / counting identity だけを扱い、first-passage geometry はまだ入れない。
-/

namespace Collatz3
namespace CSTMicro

/-- 一つの odd-only exponent を standard parity block に展開する。 -/
def parityBlock (e : ℕ) : ParityWord :=
  true :: List.replicate (e - 1) false

/-- odd-only exponent word 全体の standard parity 展開。 -/
def expandWord : Word → ParityWord
  | [] => []
  | e :: w => parityBlock e ++ expandWord w

@[simp] theorem expandWord_nil :
    expandWord ([] : Word) = [] := rfl

@[simp] theorem expandWord_cons (e : ℕ) (w : Word) :
    expandWord (e :: w) = parityBlock e ++ expandWord w := rfl

/-- parity odd-count は append で加法的。 -/
@[simp] theorem oddCount_append (u v : ParityWord) :
    oddCount (u ++ v) = oddCount u + oddCount v := by
  simp [oddCount]

/-- prefix odd-count は prefix length を越えて append の右側へ進むと加法的に分解する。 -/
theorem prefixOddCount_append_length_add
    (u v : ParityWord) (k : ℕ) :
    prefixOddCount (u ++ v) (u.length + k) =
      oddCount u + prefixOddCount v k := by
  induction u with
  | nil =>
      simp
  | cons b u ih =>
      simp only [List.cons_append, List.length_cons]
      rw [show u.length + 1 + k = (u.length + k) + 1 by omega]
      rw [prefixOddCount_cons_succ, ih]
      cases b <;> simp [oddCount, Nat.add_assoc]

/-- prefix odd-count は prefix length に関して単調。 -/
theorem prefixOddCount_mono
    (v : ParityWord)
    {a b : ℕ}
    (hab : a ≤ b) :
    prefixOddCount v a ≤ prefixOddCount v b := by
  induction v generalizing a b with
  | nil =>
      simp [prefixOddCount]
  | cons bit tail ih =>
      cases a with
      | zero =>
          simp
      | succ a =>
          cases b with
          | zero => omega
          | succ b =>
              have hab' : a ≤ b := by omega
              simpa [Nat.succ_eq_add_one] using
                Nat.add_le_add_left (ih hab') (bitNat bit)

/-- parity affine numerator は append で standard composition law を満たす。 -/
theorem affineConst_append
    (u v : ParityWord) :
    affineConst (u ++ v) =
      3 ^ oddCount v * affineConst u +
        2 ^ u.length * affineConst v := by
  induction u with
  | nil =>
      simp
  | cons b u ih =>
      cases b
      · simp [ih, pow_succ]
        ring
      · simp [ih, pow_succ, pow_add]
        ring

/-- false のみの block は affine correction を持たない。 -/
@[simp] theorem affineConst_replicate_false (n : ℕ) :
    affineConst (List.replicate n false) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih]

/-- parity block は odd bit を exactly 1 個持つ。 -/
@[simp] theorem oddCount_parityBlock (e : ℕ) :
    oddCount (parityBlock e) = 1 := by
  simp [parityBlock, oddCount]

/-- positive exponent の parity block length は exponent 自身。 -/
theorem length_parityBlock_of_pos
    {e : ℕ}
    (he : 0 < e) :
    (parityBlock e).length = e := by
  simp [parityBlock]
  omega

/-- parity block の affine correction は 1。 -/
@[simp] theorem affineConst_parityBlock (e : ℕ) :
    affineConst (parityBlock e) = 1 := by
  simp [parityBlock, oddCount]

/-- parity 展開は word append と可換。 -/
theorem expandWord_append (u v : Word) :
    expandWord (u ++ v) = expandWord u ++ expandWord v := by
  induction u with
  | nil => simp
  | cons e u ih =>
      simp [ih, List.append_assoc]

/-- parity 展開の odd-count は exponent word の odd-step 数そのもの。 -/
theorem oddCount_expandWord (w : Word) :
    oddCount (expandWord w) = Word.oddSteps w := by
  induction w with
  | nil => simp
  | cons e w ih =>
      simp [ih, Word.oddSteps]
      ring

/-- valid exponent word の parity 展開 length は total two-depth に exact に一致。 -/
theorem length_expandWord_of_valid
    {w : Word}
    (hValid : Word.Valid w) :
    (expandWord w).length = Word.twoSteps w := by
  induction w with
  | nil => simp
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Word.Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      simp [length_parityBlock_of_pos he, ih hTail, Word.twoSteps]

/-- valid word の positive prefix two-depth。 -/
theorem Word.prefixTwoDepth_pos_of_valid
    {w : Word}
    (hValid : Word.Valid w)
    {j : ℕ}
    (hjPos : 0 < j)
    (hj : j ≤ Word.oddSteps w) :
    0 < Word.prefixTwoDepth w j := by
  cases w with
  | nil =>
      simp [Word.oddSteps] at hj
      omega
  | cons e tail =>
      have he : 0 < e := hValid e (by simp)
      cases j with
      | zero => omega
      | succ j =>
          rw [Word.prefixTwoDepth_cons_succ]
          omega

/-- valid word の proper odd cut は total two-depth より strict に手前。 -/
theorem Word.prefixTwoDepth_lt_twoSteps_of_valid
    {w : Word}
    (hValid : Word.Valid w)
    {j : ℕ}
    (hj : j < Word.oddSteps w) :
    Word.prefixTwoDepth w j < Word.twoSteps w := by
  induction w generalizing j with
  | nil =>
      simp [Word.oddSteps] at hj
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Word.Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      cases j with
      | zero =>
          simp [Word.twoSteps]
          omega
      | succ j =>
          have hjTail : j < Word.oddSteps tail := by
            simpa [Word.oddSteps] using hj
          have hIH := ih hTail hjTail
          rw [Word.prefixTwoDepth_cons_succ]
          simp only [Word.twoSteps_cons]
          omega

/-- odd cut の standard time では parity prefix の odd-count が cut index に一致する。 -/
theorem prefixOddCount_expandWord_prefixTwoDepth
    {w : Word}
    (hValid : Word.Valid w)
    {j : ℕ}
    (hj : j ≤ Word.oddSteps w) :
    prefixOddCount (expandWord w) (Word.prefixTwoDepth w j) = j := by
  induction w generalizing j with
  | nil =>
      have hj0 : j = 0 := by
        simp [Word.oddSteps] at hj
        omega
      subst j
      simp
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Word.Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      cases j with
      | zero => simp
      | succ j =>
          have hjTail : j ≤ Word.oddSteps tail := by
            simpa [Word.oddSteps] using hj
          rw [Word.prefixTwoDepth_cons_succ]
          rw [expandWord_cons]
          have hLen := length_parityBlock_of_pos he
          conv_lhs =>
            congr
            · skip
            · rw [← hLen]
          rw [prefixOddCount_append_length_add]
          rw [oddCount_parityBlock, ih hTail hjTail]
          omega

/-- odd cut の直後一 step では次の odd bit が既に count される。 -/
theorem prefixOddCount_expandWord_succ_prefixTwoDepth
    {w : Word}
    (hValid : Word.Valid w)
    {j : ℕ}
    (hj : j < Word.oddSteps w) :
    prefixOddCount (expandWord w) (Word.prefixTwoDepth w j + 1) =
      j + 1 := by
  induction w generalizing j with
  | nil =>
      simp [Word.oddSteps] at hj
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Word.Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      cases j with
      | zero =>
          simp [expandWord, parityBlock, prefixOddCount, oddCount]
      | succ j =>
          have hjTail : j < Word.oddSteps tail := by
            simpa [Word.oddSteps] using hj
          rw [Word.prefixTwoDepth_cons_succ]
          rw [expandWord_cons]
          have hLen :
              (parityBlock e).length = e :=
            length_parityBlock_of_pos he
          have hIndex :
              e + Word.prefixTwoDepth tail j + 1 =
                (parityBlock e).length +
                  (Word.prefixTwoDepth tail j + 1) := by
            rw [hLen]
            omega
          rw [hIndex]
          rw [prefixOddCount_append_length_add]
          rw [oddCount_parityBlock, ih hTail hjTail]
          omega

end CSTMicro
end Collatz3
