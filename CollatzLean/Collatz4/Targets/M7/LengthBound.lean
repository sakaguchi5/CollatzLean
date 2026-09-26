import CollatzLean.Collatz4.Finite.CandidateInterval
import CollatzLean.Collatz4.Targets.M7.QBound

/-!
# Collatz4.Targets.M7.LengthBound

m=7 の残余語長の境界を一箇所に集約し、
前向き候補 `n = targetTime - r` の下端・上端・候補数をそこから導出する。

重要な点は、`12`, `4368`, `2179` を互いに独立な定数として手入力しないことである。
この三つは `4088 ≤ r ≤ 8444` と刻み2から自動的に決まる。

なお `q ≤ 1275` だけから `r` の範囲が出るわけではない。
`r` の上下限は残余語に対する別の G-bound から得るべきであり、
このファイルはその結果を有限候補列へ変換する層である。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/-- m=7 残余語長の下端。 -/
def candidateRLower : ℕ := 4088

/-- m=7 残余語長の上端。 -/
def candidateRUpper : ℕ := 8444

/-- 残余語長の刻み。偶数条件に対応する。 -/
def candidateStep : ℕ := 2

/-- `n = targetTime - r` の最小値。 -/
def candidateNLower : ℕ := targetTime - candidateRUpper

/-- `n = targetTime - r` の最大値。 -/
def candidateNUpper : ℕ := targetTime - candidateRLower

/--
下端・上端・刻みから m=7 の候補 family を生成する。
候補数は `intervalCount` で自動計算される。
-/
def candidateFamily : ArithmeticFamily :=
  intervalFamily candidateNLower candidateNUpper candidateStep

/-- m=7 の有限候補数。 -/
def candidateCount : ℕ := candidateFamily.count

/-- `Fin candidateCount` による m=7 の候補 n。 -/
def candidateN (i : Fin candidateCount) : ℕ :=
  candidateFamily.value i

/-- 同じ添字から残り語長 `r = targetTime - n` を読む。 -/
def candidateR (i : Fin candidateCount) : ℕ :=
  targetTime - candidateN i

/-- 残余語長の境界から `n` の下端12が導かれる。 -/
theorem candidateNLower_eq : candidateNLower = 12 := by
  decide

/-- 残余語長の境界から `n` の上端4368が導かれる。 -/
theorem candidateNUpper_eq : candidateNUpper = 4368 := by
  decide

/-- 境界と刻み2から候補数2179が導かれる。 -/
theorem candidateCount_eq : candidateCount = 2179 := by
  decide

/-- 候補 n の開始値は12。 -/
theorem candidateN_lower (i : Fin candidateCount) : 12 ≤ candidateN i := by
  have h := ArithmeticFamily.start_le_value candidateFamily i
  simpa [candidateN, candidateFamily, candidateNLower_eq] using h

/-- 候補 n の最大値は4368。 -/
theorem candidateN_upper (i : Fin candidateCount) : candidateN i ≤ 4368 := by
  have hi : i.1 < candidateCount := i.2
  have hc : candidateCount = 2179 := candidateCount_eq
  simp [candidateN, candidateFamily, intervalFamily,
    ArithmeticFamily.value, candidateNLower,
    candidateNUpper, candidateRLower, candidateRUpper, candidateStep,
    targetTime, intervalCount] at *
  omega

/-- 候補 n は全て偶数。 -/
theorem candidateN_even_mod (i : Fin candidateCount) : candidateN i % 2 = 0 := by
  simp [candidateN, candidateFamily, intervalFamily,
    ArithmeticFamily.value, candidateNLower,
    candidateNUpper, candidateRLower, candidateRUpper, candidateStep,
    targetTime, intervalCount, Nat.add_mod]

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
  have hn := candidateN_even_mod i
  have hu := candidateN_upper i
  simp [candidateR, targetTime] at *
  omega

/--
範囲 `12 ≤ n ≤ 4368` にある偶数 n は、必ず候補 family のどれか一つとして現れる。

これが「有限列挙に漏れがない」ことを保証する completeness theorem。
-/
theorem exists_candidateN_of_bounds_even
    {n : ℕ}
    (hlo : 12 ≤ n)
    (hhi : n ≤ 4368)
    (heven : n % 2 = 0) :
    ∃ i : Fin candidateCount, candidateN i = n := by
  let k : ℕ := (n - 12) / 2
  have hkval : 12 + 2 * k = n := by
    dsimp [k]
    omega
  have hklt : k < candidateCount := by
    rw [candidateCount_eq]
    dsimp [k]
    omega
  refine ⟨⟨k, hklt⟩, ?_⟩
  simp only [candidateN, ArithmeticFamily.value, candidateFamily, intervalFamily,
    candidateNLower,targetTime, candidateRUpper, Nat.reduceSub, candidateStep,
    intervalCount, candidateNUpper, candidateRLower,
    Nat.reduceLeDiff, ↓reduceIte, Nat.reduceDiv, Nat.reduceAdd]
  exact hkval

/--
`4088 ≤ r ≤ 8444` かつ r が偶数なら、対応する有限候補添字が必ず存在する。
同じ添字で `candidateR i = r` と `candidateN i = targetTime - r` が同時に成り立つ。
-/
theorem exists_candidate_of_residual_bounds_even
    {r : ℕ}
    (hlo : 4088 ≤ r)
    (hhi : r ≤ 8444)
    (heven : r % 2 = 0) :
    ∃ i : Fin candidateCount,
      candidateR i = r ∧ candidateN i = targetTime - r := by
  let n : ℕ := targetTime - r
  have hnlo : 12 ≤ n := by
    dsimp [n]
    simp [targetTime]
    omega
  have hnhi : n ≤ 4368 := by
    dsimp [n]
    simp [targetTime]
    omega
  have hneven : n % 2 = 0 := by
    dsimp [n]
    simp [targetTime]
    omega
  rcases exists_candidateN_of_bounds_even hnlo hnhi hneven with ⟨i, hi⟩
  refine ⟨i, ?_, ?_⟩
  · simp [candidateR, hi, n, targetTime]
    omega
  · simpa [n] using hi

end Collatz4.Targets.M7
