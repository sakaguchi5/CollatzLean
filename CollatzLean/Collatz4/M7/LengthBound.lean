import CollatzLean.Collatz4.General.CandidateInterval
import CollatzLean.Collatz4.M7.QBound

/-!
# Collatz4.M7.LengthBound

m=7 の有限候補列を、一般等差列 `ArithmeticFamily` の特殊化として定義する。

`12,14,...,4368` という具体列だけが m=7 固有で、列挙機構そのものは一般層に置く。
-/

namespace Collatz4.M7

/-- m=7 の前向き変数 `n=12,14,...,4368`。 -/
def candidateFamily : Collatz4.General.ArithmeticFamily :=
  ⟨12, 2, 2179⟩

/-- m=7 の有限候補数。一般 family の count を公開する。 -/
def candidateCount : ℕ := candidateFamily.count

/-- `Fin candidateCount` による m=7 の候補 n。 -/
def candidateN (i : Fin candidateCount) : ℕ :=
  candidateFamily.value i

/-- 同じ添字から残り語長 `r = 8456-n` を読む。 -/
def candidateR (i : Fin candidateCount) : ℕ :=
  targetTime - candidateN i

/-- 候補数は従来どおり2179。 -/
theorem candidateCount_eq : candidateCount = 2179 := by
  rfl

/-- 候補 n の開始値は12。 -/
theorem candidateN_lower (i : Fin candidateCount) : 12 ≤ candidateN i := by
  simpa [candidateN, candidateFamily] using
    (Collatz4.General.ArithmeticFamily.start_le_value candidateFamily i)

/-- 候補 n の最大値は4368。 -/
theorem candidateN_upper (i : Fin candidateCount) : candidateN i ≤ 4368 := by
  have hi : i.1 < 2179 := by
    simpa [candidateCount, candidateFamily] using i.2
  simp [candidateN, candidateFamily, Collatz4.General.ArithmeticFamily.value]
  omega

/-- 候補 n は全て偶数。 -/
theorem candidateN_even_mod (i : Fin candidateCount) : candidateN i % 2 = 0 := by
  simp [candidateN, candidateFamily, Collatz4.General.ArithmeticFamily.value, Nat.add_mod]

/-- 残り語長 r は4088以上。 -/
theorem candidateR_lower (i : Fin candidateCount) : 4088 ≤ candidateR i := by
  have h := candidateN_upper i
  simp [candidateR, targetTime]
  omega

/-- 残り語長 r は8444以下。 -/
theorem candidateR_upper (i : Fin candidateCount) : candidateR i ≤ 8444 := by
  have h := candidateN_lower i
  simp [candidateR, targetTime]
  omega

/-- 残り語長 r も偶数。 -/
theorem candidateR_even_mod (i : Fin candidateCount) : candidateR i % 2 = 0 := by
  have hi : i.1 < 2179 := by
    simpa [candidateCount, candidateFamily] using i.2
  simp [candidateR, candidateN, candidateFamily, targetTime,
    Collatz4.General.ArithmeticFamily.value]
  omega

end Collatz4.M7
