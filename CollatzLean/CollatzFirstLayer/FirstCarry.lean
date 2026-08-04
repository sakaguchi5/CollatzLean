import CollatzLean.CollatzFirstLayer.Replay

/-!
# first-carryの有限整数法則

二つの奇数が `2^d` の奇数倍だけ離れているとき、次の `3x+1` における2進深さがどう分岐するかを証明する。
`padicValNat`へ依存せず、奇数部分を明示する完全分解で記述する。
-/

namespace CollatzFirstLayer

/-- `n = 2^d u` かつ `u` が奇数であるという完全2進分解。 -/
def ExactTwoFactor (n d u : ℕ) : Prop :=
  n = 2 ^ d * u ∧ Odd u

/-- 自然数が同時に奇数かつ偶数になることはない。 -/
lemma odd_even_false_nat {n : ℕ} (ho : Odd n) (he : Even n) : False := by
  rcases ho with ⟨a, ha⟩
  rcases he with ⟨b, hb⟩
  omega

/-- 正の2冪を含む積は偶数である。 -/
lemma even_two_pow_succ_mul_nat (r v : ℕ) : Even (2 ^ (r + 1) * v) := by
  refine ⟨2 ^ r * v, ?_⟩
  rw [pow_succ]
  ring

/--
二つの2冪分解で左側の指数が真に小さいなら、
左側の残余部分には正の2冪が含まれる。
-/
lemma oddPart_eq_twoPow_mul_of_lt
    {a b u v : ℕ}
    (hpow : 2 ^ a * u = 2 ^ b * v)
    (hab : a < b) :
    ∃ r : ℕ, u = 2 ^ (r + 1) * v := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, b = a + (r + 1) := by
    refine ⟨b - a - 1, ?_⟩
    omega
  refine ⟨r, ?_⟩
  have hc :
      2 ^ a * u =
        2 ^ a * (2 ^ (r + 1) * v) := by
    calc
      2 ^ a * u = 2 ^ b * v := hpow
      _ = 2 ^ a * (2 ^ (r + 1) * v) := by
        rw [hr, pow_add]
        ring
  have hpow_pos : 0 < (2 : ℕ) ^ a := by
    exact Nat.pow_pos (by omega)
  exact Nat.mul_left_cancel hpow_pos hc


/--
完全2進分解において、一方の指数が他方より真に小さくなることはない。
小さい側の奇数部分が偶数になってしまうためである。
-/
lemma exactTwoFactor_exponent_not_lt
    {n a b u v : ℕ}
    (ha : ExactTwoFactor n a u)
    (hb : ExactTwoFactor n b v) :
    ¬a < b := by
  intro hab
  rcases ha with ⟨hna, hu⟩
  rcases hb with ⟨hnb, _⟩
  have hpow :
      2 ^ a * u = 2 ^ b * v :=
    hna.symm.trans hnb
  obtain ⟨r, hur⟩ :=
    oddPart_eq_twoPow_mul_of_lt hpow hab
  have heu : Even u := by
    rw [hur]
    exact even_two_pow_succ_mul_nat r v
  exact odd_even_false_nat hu heu


/--
完全2進分解における2冪指数は一意である。
-/
theorem exactTwoFactor_exponent_unique
    {n a b u v : ℕ}
    (ha : ExactTwoFactor n a u)
    (hb : ExactTwoFactor n b v) :
    a = b := by
  have hab : ¬a < b :=
    exactTwoFactor_exponent_not_lt ha hb
  have hba : ¬b < a :=
    exactTwoFactor_exponent_not_lt hb ha
  omega


/--
2冪指数が一致する二つの完全2進分解では、奇数部分も一致する。
-/
lemma exactTwoFactor_oddPart_unique_of_exponent_eq
    {n a b u v : ℕ}
    (ha : ExactTwoFactor n a u)
    (hb : ExactTwoFactor n b v)
    (hab : a = b) :
    u = v := by
  rcases ha with ⟨hna, _⟩
  rcases hb with ⟨hnb, _⟩
  subst b
  have hpow :
      2 ^ a * u = 2 ^ a * v :=
    hna.symm.trans hnb
  exact Nat.mul_left_cancel
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
    hpow


/--
自然数の完全2進分解は一意である。
同じ正の自然数を2冪と奇数部分に分けた二つの表示は、
指数と奇数部分がともに一致する。
-/
theorem exactTwoFactor_unique
    {n a b u v : ℕ}
    (ha : ExactTwoFactor n a u)
    (hb : ExactTwoFactor n b v) :
    a = b ∧ u = v := by
  have hab : a = b :=
    exactTwoFactor_exponent_unique ha hb
  have huv : u = v :=
    exactTwoFactor_oddPart_unique_of_exponent_eq ha hb hab
  exact ⟨hab, huv⟩
/--
下側の深さが差の深さより大きい場合、上側の次値は差の深さで正確に止まる。
-/
theorem first_carry_strict
    {x y d r a u : ℕ}
    (hr : 0 < r)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ (d + r) * a)
    (ha : Odd a) :
    ∃ b : ℕ, ExactTwoFactor (3 * y + 1) d b := by
  cases r with
  | zero => simp at hr
  | succ s =>
      rcases hu with ⟨ku, rfl⟩
      rcases ha with ⟨ka, rfl⟩
      let b := 2 ^ (s + 1) * (2 * ka + 1) + 3 * (2 * ku + 1)
      refine ⟨b, ?_, ?_⟩
      · unfold b
        calc
          3 * y + 1
              = (3 * x + 1) + 3 * 2 ^ d * (2 * ku + 1) := by
                  rw [hxy]
                  ring
          _ = 2 ^ (d + (s + 1)) * (2 * ka + 1) +
                3 * 2 ^ d * (2 * ku + 1) := by rw [hx]
          _ = 2 ^ d *
                (2 ^ (s + 1) * (2 * ka + 1) + 3 * (2 * ku + 1)) := by
                  rw [pow_add]
                  ring
      · refine ⟨2 ^ s * (2 * ka + 1) + 3 * ku + 1, ?_⟩
        unfold b
        rw [pow_succ]
        ring

/-- equal carryによって得られる、上側の追加carry商。 -/
structure FirstCarryEqualData (y d : ℕ) where
  quotient : ℕ
  equation :
    3 * y + 1 = 2 ^ (d + 1) * quotient

/--
下側の深さが差の深さと一致する場合、
上側では少なくとも1ビット余分にcarryするデータを構成する。
-/
def first_carry_equal_data
    {x y d a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ d * a)
    (ha : Odd a) :
    FirstCarryEqualData y d := by
  refine
    { quotient := (a + 3 * u) / 2
      equation := ?_ }
  -- ここではゴールがPropなのでOddの存在証明を分解できる。
  rcases hu with ⟨ku, rfl⟩
  rcases ha with ⟨ka, rfl⟩
  have hdiv :
      ((2 * ka + 1) + 3 * (2 * ku + 1)) / 2 =
        ka + 3 * ku + 2 := by
    omega
  calc
    3 * y + 1
        = (3 * x + 1) +
            3 * 2 ^ d * (2 * ku + 1) := by
              rw [hxy]
              ring
    _ = 2 ^ d * (2 * ka + 1) +
          3 * 2 ^ d * (2 * ku + 1) := by
            rw [hx]
    _ = 2 ^ d *
          ((2 * ka + 1) + 3 * (2 * ku + 1)) := by
            ring
    _ = 2 ^ (d + 1) *
          (((2 * ka + 1) + 3 * (2 * ku + 1)) / 2) := by
            rw [hdiv, pow_succ]
            ring

/--
下側の深さが差の深さと一致する場合、
上側では少なくとも1ビット余分にcarryする。
-/
theorem first_carry_equal
    {x y d a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ d * a)
    (ha : Odd a) :
    ∃ c : ℕ, 3 * y + 1 = 2 ^ (d + 1) * c := by
  let C := first_carry_equal_data hxy hu hx ha
  exact ⟨C.quotient, C.equation⟩


/-- first-carryの二分岐を一つにまとめた定理。 -/
theorem first_carry_split
    {x y d e a u : ℕ}
    (hde : d ≤ e)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    (d < e ∧ ∃ b, ExactTwoFactor (3 * y + 1) d b) ∨
    (d = e ∧ ∃ c, 3 * y + 1 = 2 ^ (d + 1) * c) := by
  rcases lt_or_eq_of_le hde with hlt | rfl
  · left
    refine ⟨hlt, ?_⟩
    let r := e - d
    have hr : 0 < r := by
      dsimp [r]
      omega
    have he : e = d + r := by
      dsimp [r]
      omega
    apply first_carry_strict (r := r) hr hxy hu
    · simpa [he] using hx
    · exact ha
  · right
    exact ⟨rfl, first_carry_equal hxy hu hx ha⟩

end CollatzFirstLayer
