import CollatzLean.CollatzFirstLayer.CarrySynchronization



/-!
# 固定点1を中心とする2進shell

`z = 1 + 2^λ u`にfirst-carryを再適用し、`v₂(z-1)`と次のodd-only指数の
関係をcaptureで直接使える形へ加工する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer

/-- 奇数`z`の固定点1からの完全2進差分。 -/
structure OneShellData (z : ℕ) where
  depth : ℕ
  oddPart : ℕ
  difference : z = 1 + 2 ^ depth * oddPart
  oddPart_odd : Odd oddPart

/-- `z`のactual一段完全分解。 -/
structure OddStepData (z : ℕ) where
  exponent : ℕ
  next : ℕ
  factorization : 3 * z + 1 = 2 ^ exponent * next
  next_odd : Odd next

namespace OneShellData

/-- shell深さが2未満なら、次指数はshell深さにexactに一致する。 -/
theorem exponent_eq_depth_of_depth_lt_two
    {z : ℕ}
    (S : OneShellData z)
    (T : OddStepData z)
    (h : S.depth < 2) :
    T.exponent = S.depth := by
  let r := 2 - S.depth
  have hr : 0 < r := by
    dsimp [r]
    omega
  have htwo : 2 = S.depth + r := by
    dsimp [r]
    omega
  have hlower : 3 * 1 + 1 = 2 ^ (S.depth + r) * 1 := by
    rw [← htwo]
    norm_num
  obtain ⟨b, hb⟩ :=
    first_carry_strict
      hr S.difference S.oddPart_odd
      hlower (by decide : Odd (1 : ℕ))
  have hactual : ExactTwoFactor (3 * z + 1) T.exponent T.next :=
    ⟨T.factorization, T.next_odd⟩
  exact exactTwoFactor_exponent_unique hactual hb

/-- shell深さが2を超えるなら、次指数はexactに2。 -/
theorem exponent_eq_two_of_two_lt_depth
    {z : ℕ}
    (S : OneShellData z)
    (T : OddStepData z)
    (h : 2 < S.depth) :
    T.exponent = 2 := by
  let C : SynchronizedCarry 1 z S.depth 2 1 S.oddPart :=
    synchronized_carry_of_depth_lt
      h S.difference S.oddPart_odd
      (by norm_num) (by decide)
  have hactual : ExactTwoFactor (3 * z + 1) T.exponent T.next :=
    ⟨T.factorization, T.next_odd⟩
  exact exactTwoFactor_exponent_unique hactual C.upperFactor

/-- shell深さが2なら、次指数は少なくとも3。 -/
theorem three_le_exponent_of_depth_eq_two
    {z : ℕ}
    (S : OneShellData z)
    (T : OddStepData z)
    (h : S.depth = 2) :
    3 ≤ T.exponent := by
  have hdiff : z = 1 + 2 ^ 2 * S.oddPart := by
    simpa [h] using S.difference
  obtain ⟨c, hc⟩ :=
    first_carry_equal
      hdiff S.oddPart_odd
      (by norm_num : 3 * 1 + 1 = 2 ^ 2 * 1)
      (by decide : Odd (1 : ℕ))
  by_contra hnot
  have hlt : T.exponent < 3 := by omega
  have hpow :
      2 ^ T.exponent * T.next = 2 ^ 3 * c := by
    calc
      2 ^ T.exponent * T.next = 3 * z + 1 := T.factorization.symm
      _ = 2 ^ (2 + 1) * c := hc
      _ = 2 ^ 3 * c := by norm_num
  obtain ⟨r, hr⟩ := oddPart_eq_twoPow_mul_of_lt hpow hlt
  have heven : Even T.next := by
    rw [hr]
    exact even_two_pow_succ_mul_nat r c
  exact odd_even_false_nat T.next_odd heven

end OneShellData

end CollatzSecondLayer2
