import CollatzLean.Collatz4.M7.QBound

/-!
# Collatz4.M7.LengthBound

残り語長 `r` の偶数範囲

`4088,4090,...,8444`

と、前向き変数 `n = 8456-r` の範囲

`12,14,...,4368`

を同じ `Fin 2179` で表す。
-/

namespace Collatz4.M7

/-- `Fin 2179` の添字から残り語長 `r` を降順に読む。 -/
def candidateR (i : Fin 2179) : ℕ :=
  8444 - 2 * i.1

/-- 残り語長は 4088 以上。 -/
theorem candidateR_lower (i : Fin 2179) : 4088 ≤ candidateR i := by
  have hi : i.1 < 2179 := i.2
  simp [candidateR]
  omega

/-- 残り語長は 8444 以下。 -/
theorem candidateR_upper (i : Fin 2179) : candidateR i ≤ 8444 := by
  simp [candidateR]

/-- 残り語長は偶数。 -/
theorem candidateR_even_mod (i : Fin 2179) : candidateR i % 2 = 0 := by
  have hi : i.1 < 2179 := i.2
  simp [candidateR]
  omega

end Collatz4.M7
