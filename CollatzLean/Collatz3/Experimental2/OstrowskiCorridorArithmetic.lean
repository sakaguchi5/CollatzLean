import CollatzLean.Collatz3.Experimental2.FiniteInverseCorridorComposition

/-!
# Collatz3 Experimental2: Ostrowski 型 digit 算術と corridor 座標

continued fraction そのものをこの層で再実装せず、Ostrowski numeration が
現在の corridor 証明に与える最小算術だけを抽出する。

convergent denominator の局所再帰

`Qnext = a * Q + Qprev`

と greedy residual `R < Qnext` から、

* greedy digit `R / Q` は `a` 以下、
* 最大 digit `a` を使った後の residual は `Qprev` 未満、
* 従って次の低位 digit は `0`

が従う。これは標準 Ostrowski digit legality の局所形である。

後半では `(P,Q,coeff)` の有限 digit block 列を、実際の corridor 列へ展開する。
最小の非零 digit を最後の endpoint block として分離すれば、

`N = Σ c_n Q_n`

に対して scalar height は

`H(N) = Σ c_n P_n + ε`

となり、`ε` は最後の endpoint correction 一個だけである。
この `ε` が `ε(min supp c)` に対応する。
-/

namespace Collatz3
namespace Experimental2

/-- residual `R` に対する greedy digit。 -/
def ostrowskiGreedyDigit (R Q : ℕ) : ℕ := R / Q

/-- greedy digit を一つ引いた残差。 -/
def ostrowskiGreedyResidual (R Q : ℕ) : ℕ :=
  R - ostrowskiGreedyDigit R Q * Q

/--
continued-fraction denominator 再帰の一段から greedy digit の標準上限が出る。

`Qprev < Q`, `Qnext = aQ + Qprev`, `R < Qnext` なら `R/Q ≤ a`。
-/
theorem ostrowskiGreedyDigit_le_partialQuotient
    {Qprev Q Qnext a R : ℕ}
    (hQ : 0 < Q)
    (hPrev : Qprev < Q)
    (hRec : Qnext = a * Q + Qprev)
    (hR : R < Qnext) :
    ostrowskiGreedyDigit R Q ≤ a := by
  unfold ostrowskiGreedyDigit
  by_contra hNot
  have hDigit : a + 1 ≤ R / Q := by omega
  have hMul : (a + 1) * Q ≤ R :=
    (Nat.le_div_iff_mul_le hQ).1 hDigit
  have hNextLt : Qnext < (a + 1) * Q := by
    calc
      Qnext = a * Q + Qprev := hRec
      _ < a * Q + Q := Nat.add_lt_add_left hPrev _
      _ = (a + 1) * Q := by ring
  omega

/--
greedy digit が最大値 `a` に達したとき、引き算後の residual は `Qprev` 未満。

これは Ostrowski の「最大 digit の直後の低位 digit は 0」という規則の核心。
-/
theorem ostrowskiGreedyResidual_lt_previousWeight_of_maxDigit
    {Qprev Q Qnext a R : ℕ}
    (hPrevPos : 0 < Qprev)
    (hRec : Qnext = a * Q + Qprev)
    (hR : R < Qnext)
    (hMax : ostrowskiGreedyDigit R Q = a) :
    ostrowskiGreedyResidual R Q < Qprev := by
  unfold ostrowskiGreedyResidual
  rw [hMax]
  rw [hRec] at hR
  omega

/-- 最大 digit の次の低位 greedy digit は exact に `0`。 -/
theorem ostrowskiPreviousGreedyDigit_eq_zero_of_maxDigit
    {Qprev Q Qnext a R : ℕ}
    (hPrevPos : 0 < Qprev)
    (hRec : Qnext = a * Q + Qprev)
    (hR : R < Qnext)
    (hMax : ostrowskiGreedyDigit R Q = a) :
    ostrowskiGreedyDigit (ostrowskiGreedyResidual R Q) Qprev = 0 := by
  unfold ostrowskiGreedyDigit
  exact Nat.div_eq_of_lt
    (ostrowskiGreedyResidual_lt_previousWeight_of_maxDigit
      hPrevPos hRec hR hMax)

/--
Ostrowski の一桁を corridor 座標 `(P,Q)` と係数 `coeff` で表す最小 data。

continued fraction の証明書や orientation は保存しない。
それらは別 theorem がこの digit block に exact corridor law を供給する。
-/
structure OstrowskiCorridorDigit where
  P : ℕ
  Q : ℕ
  coeff : ℕ

/-- 高位から低位へ並んだ digit block を実際の corridor 列へ展開する。 -/
def expandOstrowskiCorridorDigits :
    List OstrowskiCorridorDigit → List (ℕ × ℕ)
  | [] => []
  | d :: ds =>
      List.replicate d.coeff (d.P, d.Q) ++
        expandOstrowskiCorridorDigits ds

/-- Ostrowski 型表示の `P` 側 weighted sum。 -/
def ostrowskiPSum : List OstrowskiCorridorDigit → ℕ
  | [] => 0
  | d :: ds => d.coeff * d.P + ostrowskiPSum ds

/-- Ostrowski 型表示の `Q` 側 weighted sum。 -/
def ostrowskiQSum : List OstrowskiCorridorDigit → ℕ
  | [] => 0
  | d :: ds => d.coeff * d.Q + ostrowskiQSum ds

/-- digit 展開後の corridor `P` 総和は weighted `P` sum に一致する。 -/
theorem corridorPSum_expandOstrowskiCorridorDigits :
    ∀ ds : List OstrowskiCorridorDigit,
      corridorPSum (expandOstrowskiCorridorDigits ds) = ostrowskiPSum ds
  | [] => by simp [expandOstrowskiCorridorDigits, ostrowskiPSum]
  | d :: ds => by
      simp [expandOstrowskiCorridorDigits, ostrowskiPSum,
        corridorPSum_append,
        corridorPSum_expandOstrowskiCorridorDigits ds]

/-- digit 展開後の corridor `Q` 総和も weighted `Q` sum に一致する。 -/
theorem corridorQSum_expandOstrowskiCorridorDigits :
    ∀ ds : List OstrowskiCorridorDigit,
      corridorQSum (expandOstrowskiCorridorDigits ds) = ostrowskiQSum ds
  | [] => by simp [expandOstrowskiCorridorDigits, ostrowskiQSum]
  | d :: ds => by
      simp [expandOstrowskiCorridorDigits, ostrowskiQSum,
        corridorQSum_append,
        corridorQSum_expandOstrowskiCorridorDigits ds]

/--
高位 digit 列 `higher` と、最小非零 digit `(P,Q,d)` を分離した有限 Ostrowski 型住所。

`d>0` とし、最小 digit の最後の一個を endpoint `Q` として残す。
高位 digit 全体と `d-1` 個の同一 block が exact corridor chain を作るなら、

`H(Σ higher_Q + dQ) = Σ higher_P + dP + ε`

となる。

`ε` は最小非零 digit の endpoint correction だけであり、
途中の orientation correction は scalar height には蓄積しない。
-/
theorem finiteOstrowskiCorridor_height_formula
    {H : ℕ → ℕ}
    (higher : List OstrowskiCorridorDigit)
    {P Q d ε : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain H
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (hEnd : H Q = P + ε) :
    H (ostrowskiQSum higher + d * Q) =
      ostrowskiPSum higher + d * P + ε := by
  have h := exactInverseCorridorChain_to_endpoint
    (H := H)
    (xs := expandOstrowskiCorridorDigits higher ++
      List.replicate (d - 1) (P, Q))
    (P := P) (Q := Q) (ε := ε) C hEnd
  rw [corridorQSum_append, corridorPSum_append,
    corridorQSum_expandOstrowskiCorridorDigits,
    corridorPSum_expandOstrowskiCorridorDigits,
    corridorQSum_replicate, corridorPSum_replicate] at h
  have hdEq : d - 1 + 1 = d := by omega
  have hQEq : (d - 1) * Q + Q = d * Q := by
    calc
      (d - 1) * Q + Q = (d - 1 + 1) * Q := by ring
      _ = d * Q := by rw [hdEq]
  have hPEq : (d - 1) * P + P = d * P := by
    calc
      (d - 1) * P + P = (d - 1 + 1) * P := by ring
      _ = d * P := by rw [hdEq]
  have hQTotal :
      ostrowskiQSum higher + (d - 1) * Q + Q =
        ostrowskiQSum higher + d * Q := by
    calc
      ostrowskiQSum higher + (d - 1) * Q + Q
          = ostrowskiQSum higher + ((d - 1) * Q + Q) := by
              omega
      _ = ostrowskiQSum higher + d * Q := by
            rw [hQEq]
  have hPTotal :
      ostrowskiPSum higher + (d - 1) * P + P =
        ostrowskiPSum higher + d * P := by
    calc
      ostrowskiPSum higher + (d - 1) * P + P
          = ostrowskiPSum higher + ((d - 1) * P + P) := by
              omega
      _ = ostrowskiPSum higher + d * P := by
            rw [hPEq]
  rw [hQTotal, hPTotal] at h
  exact h

/-- 最小非零 digit が lower endpoint なら補正は `0`。 -/
theorem finiteOstrowskiCorridor_height_formula_lower
    {H : ℕ → ℕ}
    (higher : List OstrowskiCorridorDigit)
    {P Q d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain H
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (hEnd : H Q = P) :
    H (ostrowskiQSum higher + d * Q) =
      ostrowskiPSum higher + d * P := by
  have h := finiteOstrowskiCorridor_height_formula
    (H := H) higher (P := P) (Q := Q) (d := d) (ε := 0)
    hd C (by simpa using hEnd)
  simpa using h

/-- 最小非零 digit が upper endpoint なら補正は exact に `1`。 -/
theorem finiteOstrowskiCorridor_height_formula_upper
    {H : ℕ → ℕ}
    (higher : List OstrowskiCorridorDigit)
    {P Q d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain H
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (hEnd : H Q = P + 1) :
    H (ostrowskiQSum higher + d * Q) =
      ostrowskiPSum higher + d * P + 1 := by
  exact finiteOstrowskiCorridor_height_formula
    (H := H) higher (P := P) (Q := Q) (d := d) (ε := 1)
    hd C hEnd

/--
一つの Ostrowski digit を同じ sharp corridor の反復だけで閉じるための wrapper。

`d` 個の `Q` を使う場合、最後の一個を endpoint に残すので、
positive translation が必要なのは `(d-1)Q < Qnext` までである。
-/
theorem oneOstrowskiDigit_height_formula
    {H : ℕ → ℕ}
    {P Q Qnext d ε : ℕ}
    (hd : 0 < d)
    (hQPos : 0 < Q)
    (hRange : (d - 1) * Q < Qnext)
    (hTranslate : ∀ k : ℕ, 0 < k → k < Qnext →
      H (Q + k) = P + H k)
    (hEnd : H Q = P + ε) :
    H (d * Q) = d * P + ε :=
  repeatedCorridor_to_endpoint hd hQPos hRange hTranslate hEnd

end Experimental2
end Collatz3
