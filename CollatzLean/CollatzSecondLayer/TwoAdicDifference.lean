import CollatzLean.CollatzSecondLayer.PreparedCarry

/-!
# 正の自然数差の完全2進分解

chain extractionで得られる正の奇数値差を、`ExactTwoFactor`および
`OrderedDifferenceData`へ変換するための一般補題をまとめる。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 正の自然数は2冪と奇数部分へ分解できる。 -/
theorem exists_exactTwoFactor_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    ∃ d u : ℕ, ExactTwoFactor n d u := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases Nat.even_or_odd n with heven | hodd
      · rcases heven with ⟨m, hm⟩
        have hmpos : 0 < m := by
          omega
        have hmlt : m < n := by
          omega
        obtain ⟨d, u, hfactor⟩ := ih m hmlt hmpos
        rcases hfactor with ⟨hmu, hu⟩
        refine ⟨d + 1, u, ?_, hu⟩
        rw [hm, hmu, pow_succ]
        ring
      · exact ⟨0, n, by simp [ExactTwoFactor, hodd]⟩

/-- 正の偶数の完全2進深さは正。 -/
theorem exactTwoFactor_depth_pos_of_even
    {n d u : ℕ}
    (hn : Even n)
    (hfactor : ExactTwoFactor n d u) :
    0 < d := by
  by_contra hnot
  have hd : d = 0 := by omega
  subst d
  have hnodd : Odd n := by
    rcases hfactor with ⟨h, hu⟩
    have hnu : n = u := by
      simpa using h
    simpa [hnu] using hu
  exact odd_even_false_nat hnodd hn

/-- 二つの奇数の正の差は正深さを持つ完全2進分解を持つ。 -/
theorem exists_positive_exactTwoFactor_of_odd_lt
    {x y : ℕ}
    (hx : Odd x)
    (hy : Odd y)
    (hxy : x < y) :
    ∃ d u : ℕ,
      0 < d ∧
      y = x + 2 ^ d * u ∧
      Odd u := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have heven : Even (y - x) := by
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    refine ⟨b - a, ?_⟩
    omega
  obtain ⟨d, u, hfactor⟩ :=
    exists_exactTwoFactor_of_pos hpos
  have hd : 0 < d :=
    exactTwoFactor_depth_pos_of_even heven hfactor
  rcases hfactor with ⟨hdifference, hu⟩
  refine ⟨d, u, hd, ?_, hu⟩
  omega

/--
正深さを持つ完全2進差分の存在証明から
`OrderedDifferenceData`を構成する。
-/
noncomputable def orderedDifferenceDataOfExists
    (T : TerminalPairData)
    (hex :
      ∃ d u : ℕ,
        0 < d ∧
        T.YAR = T.YA + 2 ^ d * u ∧
        Odd u) :
    OrderedDifferenceData T := by
  let d : ℕ :=
    Classical.choose hex
  have hdSpec :
      ∃ u : ℕ,
        0 < d ∧
        T.YAR = T.YA + 2 ^ d * u ∧
        Odd u := by
    simpa [d] using Classical.choose_spec hex
  let u : ℕ :=
    Classical.choose hdSpec
  have hSpec :
      0 < d ∧
      T.YAR = T.YA + 2 ^ d * u ∧
      Odd u := by
    simpa [u] using Classical.choose_spec hdSpec
  exact
    { depth := d
      oddPart := u
      depth_pos := hSpec.1
      difference := hSpec.2.1
      oddPart_odd := hSpec.2.2 }

/-- 二つの連続するrunを語の連結に沿って合成する。 -/
theorem runs_append
    {A R : ExpWord}
    {X Y Z : ℕ}
    (hA : Runs A X Y)
    (hR : Runs R Y Z) :
    Runs (A ++ R) X Z := by
  induction hA with
  | nil x =>
      simpa using hR
  | @cons e w x y z he hstep hy htail ih =>
      simp only [List.cons_append]
      exact Runs.cons he hstep hy (ih hR)

/-- terminal pairのprefix runとsuffix runを連結した全体run。 -/
theorem TerminalPairData.total_run
    (T : TerminalPairData) :
    Runs (T.A ++ T.R) T.X T.YAR := by
  exact runs_append T.runA T.runR

/--
正順序を持つterminal pairから`OrderedDifferenceData`を構成する。
-/
noncomputable def orderedDifferenceDataOfLt
    (T : TerminalPairData)
    (hlt : T.YA < T.YAR) :
    OrderedDifferenceData T := by
  have hYAodd : Odd T.YA :=
    T.runA.end_odd_of_ne_nil T.A_nonempty
  have hYARodd : Odd T.YAR :=
    T.total_run.end_odd_of_ne_nil T.total_nonempty
  exact orderedDifferenceDataOfExists T
    (exists_positive_exactTwoFactor_of_odd_lt
      hYAodd
      hYARodd
      hlt)
/--
奇数部分が奇数である完全分解の指数より深い2冪で同じ数を割ることはできない。
-/
theorem factor_exponent_le_exact_exponent
    {n exactDepth divisorDepth oddPart quotient : ℕ}
    (hexact : ExactTwoFactor n exactDepth oddPart)
    (hfactor : n = 2 ^ divisorDepth * quotient) :
    divisorDepth ≤ exactDepth := by
  by_contra hnot
  have hlt : exactDepth < divisorDepth := by omega
  rcases hexact with ⟨hn, hodd⟩
  have hpowers :
      2 ^ exactDepth * oddPart =
        2 ^ divisorDepth * quotient := by
    rw [← hn, hfactor]
  obtain ⟨r, hoddPart⟩ :=
    oddPart_eq_twoPow_mul_of_lt hpowers hlt
  have heven : Even oddPart := by
    rw [hoddPart]
    exact even_two_pow_succ_mul_nat r quotient
  exact odd_even_false_nat hodd heven

end CollatzSecondLayer
