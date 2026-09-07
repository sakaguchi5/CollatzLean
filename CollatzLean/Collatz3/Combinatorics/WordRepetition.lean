import CollatzLean.Collatz3.Core.Word

/-!
# Collatz3: exponent word の組合せ的反復

actual Collatz orbit の周期とは完全に分離した文字列側の語彙。
`wordPower baseWord copies` は `baseWord` を `copies` 回連結した word。
-/

namespace Collatz3
namespace Word

/-- `baseWord` を `copies` 回連結した word。 -/
def wordPower (baseWord : Word) : ℕ → Word
  | 0 => []
  | copies + 1 => baseWord ++ wordPower baseWord copies

@[simp] theorem wordPower_zero (baseWord : Word) :
    wordPower baseWord 0 = [] := rfl

@[simp] theorem wordPower_succ (baseWord : Word) (copies : ℕ) :
    wordPower baseWord (copies + 1) =
      baseWord ++ wordPower baseWord copies := rfl

/-- 少なくとも 2 回の同一 block 連結として表せる word。 -/
def IsNontrivialWordPower (w baseWord : Word) : Prop :=
  baseWord ≠ [] ∧
    ∃ copies : ℕ,
      2 ≤ copies ∧
      w = wordPower baseWord copies

/-- word power の odd-step 数。 -/
@[simp] theorem oddSteps_wordPower (baseWord : Word) (copies : ℕ) :
    oddSteps (wordPower baseWord copies) =
      copies * oddSteps baseWord := by
  induction copies with
  | zero =>
      simp [wordPower]
  | succ copies ih =>
      simp [wordPower, ih, Nat.succ_mul]
      ac_rfl

/-- word power の two-step 数。 -/
@[simp] theorem twoSteps_wordPower (baseWord : Word) (copies : ℕ) :
    twoSteps (wordPower baseWord copies) =
      copies * twoSteps baseWord := by
  induction copies with
  | zero =>
      simp [wordPower]
  | succ copies ih =>
      simp [wordPower, ih, Nat.succ_mul]
      ac_rfl

/-- valid block の有限 power は valid。 -/
theorem Valid.wordPower
    {baseWord : Word}
    (hBase : Valid baseWord)
    (copies : ℕ) :
    Valid (wordPower baseWord copies) := by
  induction copies with
  | zero =>
      simp [Valid]
  | succ copies ih =>
      simpa [wordPower] using hBase.append ih

end Word
end Collatz3
