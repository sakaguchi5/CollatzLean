import CollatzLean.CollatzFirstLayer.DepthCoefficient
import CollatzLean.CollatzSecondLayer.FutureMinimum

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.List.OfFn
import Mathlib.Order.KonigLemma
import Mathlib.Tactic.DeriveFintype
/-!
# moving-anchorの2進コンパクト化

非有界odd-only軌道からfuture-minimum列を構成し、各固定長の指数語と
各2冪剰余が安定する無限部分列をKőnigの無限補題で抽出する。

このファイルでは `MovingCompactnessPrinciple` を仮定として残さず、
最後に `movingCompactnessPrinciple` として証明する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord
open scoped BigOperators

/-- 無限指数列`E`の先頭`m`文字。 -/
def prefixWord (E : ℕ → ℕ) : ℕ → ExpWord
  | 0 => []
  | m + 1 => E 0 :: prefixWord (fun n => E (n + 1)) m

@[simp] theorem prefixWord_zero (E : ℕ → ℕ) :
    prefixWord E 0 = [] := rfl

@[simp] theorem prefixWord_succ (E : ℕ → ℕ) (m : ℕ) :
    prefixWord E (m + 1) =
      E 0 :: prefixWord (fun n => E (n + 1)) m := rfl

@[simp] theorem prefixWord_length (E : ℕ → ℕ) (m : ℕ) :
    (prefixWord E m).length = m := by
  induction m generalizing E with
  | zero => rfl
  | succ m ih => simp [prefixWord, ih]

/-- `prefixWord`を`List.ofFn`表示へ直す。 -/
theorem prefixWord_eq_ofFn (E : ℕ → ℕ) (m : ℕ) :
    prefixWord E m = List.ofFn (fun i : Fin m => E i.1) := by
  induction m generalizing E with
  | zero => simp
  | succ m ih =>
      rw [prefixWord_succ, List.ofFn_succ]
      congr 1
      simpa [Function.comp_def, Nat.add_assoc] using
        ih (E := fun n => E (n + 1))

/-- 長い極限prefixの先頭を取ると短い極限prefixになる。 -/
theorem prefixWord_take_of_le (E : ℕ → ℕ)
    {m n : ℕ} (h : m ≤ n) :
    (prefixWord E n).take m = prefixWord E m := by
  induction m generalizing E n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [prefixWord_succ, List.take_succ_cons]
          rw [ih (E := fun k => E (k + 1)) (n := n) (by omega)]

/-- 正の無限指数列の有限prefixは有効語である。 -/
theorem prefixWord_valid
    {E : ℕ → ℕ} (hE : ∀ n, 0 < E n) (m : ℕ) :
    Valid (prefixWord E m) := by
  induction m generalizing E with
  | zero => simp [Valid]
  | succ m ih =>
      intro e he
      simp only [prefixWord_succ, List.mem_cons] at he
      rcases he with rfl | he
      · exact hE 0
      · exact ih (E := fun n => E (n + 1))
          (fun n => hE (n + 1)) e he

/-- `Z₂` の元を、互いに整合する有限剰余の塔だけで表す。 -/
structure CoherentTwoAdicShadow where
  residue : ℕ → ℕ
  residue_lt : ∀ r, residue r < 2 ^ r
  compatible : ∀ r,
    residue (r + 1) % 2 ^ r = residue r

/-- moving anchor列が整合剰余系へ2進収束すること。 -/
def ConvergesToShadow
    (a : ℕ → ℕ) (ξ : CoherentTwoAdicShadow) : Prop :=
  ∀ r : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
    a j % 2 ^ r = ξ.residue r

/-- moving-anchor解析で固定するデータ。 -/
structure MovingLimitData (O : OddOrbit) where
  minima : O.FutureMinimumSequence
  shadow : CoherentTwoAdicShadow
  shadow_convergence :
    ConvergesToShadow
      (fun j => O.value (minima.index j)) shadow
  limitExponent : ℕ → ℕ
  limitExponent_pos : ∀ n, 0 < limitExponent n
  prefix_stabilizes :
    ∀ m : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      O.segmentWord (minima.index j) m =
        prefixWord limitExponent m

namespace MovingLimitData

/-- 極限指数語の長さ`m`prefix。 -/
def limitWord {O : OddOrbit} (D : MovingLimitData O) (m : ℕ) : ExpWord :=
  prefixWord D.limitExponent m

@[simp] theorem limitWord_length {O : OddOrbit}
    (D : MovingLimitData O) (m : ℕ) :
    (D.limitWord m).length = m := by
  simp [limitWord]

/-- 極限指数語の有限prefixは有効。 -/
theorem limitWord_valid {O : OddOrbit}
    (D : MovingLimitData O) (m : ℕ) :
    Valid (D.limitWord m) := by
  exact prefixWord_valid D.limitExponent_pos m

end MovingLimitData

namespace OddOrbit

/-- 同じ奇数に対する完全2進分解は一意なので、次の指数と次値も一意である。 -/
lemma next_data_unique
    {x e₁ e₂ y₁ y₂ : ℕ}
    (h₁ : 2 ^ e₁ * y₁ = 3 * x + 1)
    (h₂ : 2 ^ e₂ * y₂ = 3 * x + 1)
    (hy₁ : Odd y₁) (hy₂ : Odd y₂) :
    e₁ = e₂ ∧ y₁ = y₂ := by
  have hfac₁ : ExactTwoFactor (3 * x + 1) e₁ y₁ :=
    ⟨h₁.symm, hy₁⟩
  have hfac₂ : ExactTwoFactor (3 * x + 1) e₂ y₂ :=
    ⟨h₂.symm, hy₂⟩
  exact exactTwoFactor_unique hfac₁ hfac₂

/-- 軌道値が二位置で一致すれば、その後の全軌道も一致する。 -/
theorem value_eq_propagates
    (O : OddOrbit) {n m : ℕ}
    (h : O.value n = O.value m) :
    ∀ k : ℕ, O.value (n + k) = O.value (m + k) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have h₁ :
          2 ^ O.exponent (n + k) * O.value (n + k + 1) =
            3 * O.value (n + k) + 1 := by
        simpa [Nat.add_assoc] using O.step (n + k)
      have h₂ :
          2 ^ O.exponent (m + k) * O.value (m + k + 1) =
            3 * O.value (n + k) + 1 := by
        calc
          2 ^ O.exponent (m + k) * O.value (m + k + 1)
              = 3 * O.value (m + k) + 1 := by
                  simpa [Nat.add_assoc] using O.step (m + k)
          _ = 3 * O.value (n + k) + 1 := by rw [ih]
      have hu := next_data_unique h₁ h₂
          (O.value_odd (n + k + 1))
          (O.value_odd (m + k + 1))
      simpa [Nat.add_assoc] using hu.2

/-- 二位置の一致から得られる周期差による一段後退公式。 -/
lemma value_eq_sub_period
    (O : OddOrbit) {n m t : ℕ}
    (hnm : n < m)
    (h : O.value n = O.value m)
    (ht : m ≤ t) :
    O.value t = O.value (t - (m - n)) := by
  let k := t - m
  have htm : t = m + k := by
    dsimp [k]
    omega
  have hnk : t - (m - n) = n + k := by
    dsimp [k]
    omega
  have hp :
      O.value (n + k) = O.value (m + k) :=
    O.value_eq_propagates h k
  calc
    O.value t
        = O.value (m + k) := by rw [htm]
    _ = O.value (n + k) := hp.symm
    _ = O.value (t - (m - n)) := by rw [hnk]

/-- 非有界軌道では、より後ろの位置で同じ値を再訪できない。 -/
lemma value_ne_of_lt_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded)
    {n m : ℕ} (hlt : n < m) :
    O.value n ≠ O.value m := by
  intro hnm
  let d := m - n
  let B :=
    Finset.sum (Finset.range m) (fun i => O.value i)
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hbound : ∀ t : ℕ, O.value t ≤ B := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        by_cases htm : t < m
        · dsimp [B]
          exact Finset.single_le_sum
            (fun i _ => Nat.zero_le (O.value i))
            (Finset.mem_range.mpr htm)
        · have hmt : m ≤ t := Nat.le_of_not_gt htm
          have hsub : t - d < t := by
            apply Nat.sub_lt
            · omega
            · exact hd
          rw [O.value_eq_sub_period hlt hnm hmt]
          exact ih (t - d) hsub
  obtain ⟨t, ht⟩ := hU B
  exact Nat.not_lt_of_ge (hbound t) ht

/-- 非有界軌道では同じ値を二度取れない。 -/
theorem value_injective_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded) :
    Function.Injective O.value := by
  intro n m hnm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact False.elim ((O.value_ne_of_lt_of_unbounded hU hlt) hnm)
  · exact heq
  · exact False.elim ((O.value_ne_of_lt_of_unbounded hU hgt) hnm.symm)

/-- 非有界軌道は実際には任意の固定上界から最終的に脱出する。 -/
theorem escapesToInfinity_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded) :
    O.EscapesToInfinity := by
  intro M
  have hinj : Function.Injective O.value :=
    O.value_injective_of_unbounded hU
  let Bad := {n : ℕ // O.value n ≤ M}
  let toFin : Bad → Fin (M + 1) :=
    fun n => ⟨O.value n.1, Nat.lt_succ_of_le n.2⟩
  have htoFin : Function.Injective toFin := by
    intro a b hab
    apply Subtype.ext
    apply hinj
    exact congrArg Fin.val hab
  letI : Finite Bad :=
    Finite.of_injective toFin htoFin
  letI : Fintype Bad :=
    Fintype.ofFinite Bad
  let N : ℕ :=
    Finset.sum Finset.univ (fun x : Bad => x.1 + 1)
  refine ⟨N, ?_⟩
  intro n hn
  by_contra hnot
  have hbad : O.value n ≤ M :=
    Nat.le_of_not_gt hnot
  let x : Bad := ⟨n, hbad⟩
  have hx : n + 1 ≤ N := by
    dsimp [N]
    simpa [x] using
      (Finset.single_le_sum
        (fun y (_ : y ∈ (Finset.univ : Finset Bad)) =>
          Nat.zero_le (y.1 + 1))
        (Finset.mem_univ x))
  omega

/-- 閾値以後に現れる軌道値が少なくとも一つ存在する。 -/
lemma exists_tail_value (O : OddOrbit) (N : ℕ) :
    ∃ v : ℕ, ∃ n : ℕ, N ≤ n ∧ O.value n = v :=
  ⟨O.value N, N, le_rfl, rfl⟩

/-- 閾値以後に現れる値の最小値。 -/
noncomputable def tailMinValue
    (O : OddOrbit)
    (N : ℕ) : ℕ := by
  classical
  exact Nat.find (O.exists_tail_value N)

lemma tailMinValue_spec
    (O : OddOrbit)
    (N : ℕ) :
    ∃ n : ℕ,
      N ≤ n ∧
      O.value n = tailMinValue O N := by
  classical
  unfold tailMinValue
  exact Nat.find_spec (O.exists_tail_value N)

/-- `tailMinValue`を実現する最初の証人位置を一つ選ぶ。 -/
noncomputable def tailMinIndex
    (O : OddOrbit)
    (N : ℕ) : ℕ :=
  Classical.choose (tailMinValue_spec O N)

/-- `tailMinIndex`は閾値以後にある。 -/
lemma tailMinIndex_ge
    (O : OddOrbit)
    (N : ℕ) :
    N ≤ tailMinIndex O N := by
  exact (Classical.choose_spec (tailMinValue_spec O N)).1

/-- `tailMinIndex`ではtail最小値が実現される。 -/
lemma value_tailMinIndex
    (O : OddOrbit)
    (N : ℕ) :
    O.value (tailMinIndex O N) = tailMinValue O N := by
  exact (Classical.choose_spec (tailMinValue_spec O N)).2

/-- tailの最小値は、閾値以後の任意の軌道値以下である。 -/
lemma tailMinValue_le
    (O : OddOrbit) (N m : ℕ)
    (hm : N ≤ m) :
    O.tailMinValue N ≤ O.value m := by
  classical
  unfold tailMinValue
  exact Nat.find_min'
    (O.exists_tail_value N)
    ⟨m, hm, rfl⟩

/-- 閾値以後の最小値を再帰的に取り続ける位置列。 -/
noncomputable def futureMinIndex (O : OddOrbit) : ℕ → ℕ
  | 0 => O.tailMinIndex 0
  | j + 1 => O.tailMinIndex (O.futureMinIndex j + 1)

lemma futureMinIndex_lt_succ (O : OddOrbit) (j : ℕ) :
    O.futureMinIndex j < O.futureMinIndex (j + 1) := by
  rw [futureMinIndex]
  have h := O.tailMinIndex_ge (O.futureMinIndex j + 1)
  omega

lemma futureMinIndex_strict (O : OddOrbit) :
    StrictMono O.futureMinIndex :=
  strictMono_nat_of_lt_succ O.futureMinIndex_lt_succ

lemma futureMinIndex_ge_id (O : OddOrbit) (j : ℕ) :
    j ≤ O.futureMinIndex j := by
  induction j with
  | zero => omega
  | succ j ih =>
      have h := O.futureMinIndex_lt_succ j
      omega

lemma futureMinIndex_is_futureMinimum
    (O : OddOrbit) (j : ℕ) :
    O.FutureMinimumAt (O.futureMinIndex j) := by
  intro m hm
  cases j with
  | zero =>
      rw [futureMinIndex, O.value_tailMinIndex]
      exact O.tailMinValue_le 0 m (by omega)
  | succ j =>
      rw [futureMinIndex, O.value_tailMinIndex]
      exact O.tailMinValue_le (O.futureMinIndex j + 1) m
        (by
          have h := O.futureMinIndex_lt_succ j
          omega)

/-- 非有界軌道からfuture-minimum列を構成する。 -/
noncomputable def futureMinimumSequenceOfUnbounded
    (O : OddOrbit) (hU : O.Unbounded) :
    O.FutureMinimumSequence where
  index := O.futureMinIndex
  index_strict := O.futureMinIndex_strict
  futureMinimum := O.futureMinIndex_is_futureMinimum
  value_strict := by
    intro i j hij
    have hle :
        O.value (O.futureMinIndex i) ≤
          O.value (O.futureMinIndex j) :=
      O.futureMinIndex_is_futureMinimum i _
        ((O.futureMinIndex_strict hij).le)
    have hne :
        O.value (O.futureMinIndex i) ≠
          O.value (O.futureMinIndex j) := by
      intro heq
      have hinj := O.value_injective_of_unbounded hU heq
      exact (O.futureMinIndex_strict hij).ne hinj
    exact lt_of_le_of_ne hle hne
  eventually_large := by
    intro M J
    obtain ⟨N, hN⟩ := O.escapesToInfinity_of_unbounded hU M
    let j := max J N
    refine ⟨j, le_max_left _ _, ?_⟩
    apply hN
    exact le_trans (le_max_right _ _) (O.futureMinIndex_ge_id j)

/-- 正の指数に対する2冪は少なくとも2である。 -/
lemma two_le_twoPow_of_pos
    {e : ℕ}
    (he : 0 < e) :
    2 ≤ 2 ^ e := by
  cases e with
  | zero =>
      omega
  | succ r =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ r :=
        Nat.pow_pos (by omega)
      omega


/--
奇数軌道の一段後の値は、現在値の2倍以下である。

指数が正なので分母には少なくとも2が含まれ、
`3x + 1 ≤ 4x`を用いる。
-/
lemma next_value_le_two_mul
    (O : OddOrbit)
    (i : ℕ) :
    O.value (i + 1) ≤ 2 * O.value i := by
  have hxpos : 0 < O.value i :=
    O.value_pos i
  have hepos : 0 < O.exponent i :=
    O.exponent_pos i
  have hpow :
      2 ≤ 2 ^ O.exponent i :=
    two_le_twoPow_of_pos hepos
  have htwo :
      2 * O.value (i + 1) ≤
        3 * O.value i + 1 := by
    calc
      2 * O.value (i + 1)
          ≤ 2 ^ O.exponent i * O.value (i + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * O.value i + 1 :=
        O.step i
  have hfour :
      3 * O.value i + 1 ≤
        4 * O.value i := by
    omega
  omega


/--
任意の位置から`k`段後の値は、
開始値の`2^k`倍以下である。
-/
lemma value_add_le_twoPow_mul
    (O : OddOrbit)
    (n : ℕ) :
    ∀ k : ℕ,
      O.value (n + k) ≤
        2 ^ k * O.value n := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hnext :
          O.value (n + k + 1) ≤
            2 * O.value (n + k) :=
        next_value_le_two_mul O (n + k)
      calc
        O.value (n + (k + 1))
            = O.value (n + k + 1) := by
                congr 1
        _ ≤ 2 * O.value (n + k) :=
          hnext
        _ ≤ 2 * (2 ^ k * O.value n) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) * O.value n := by
          rw [pow_succ]
          ring

/-- future-minimumから`k`段後の値は開始値の`2^k`倍以下。 -/
lemma segment_value_le
    (O : OddOrbit)
    {n : ℕ}
    (_hmin : O.FutureMinimumAt n) :
    ∀ k : ℕ,
      O.value (n + k) ≤
        2 ^ k * O.value n := by
  clear _hmin
  exact value_add_le_twoPow_mul O n

/--
`x > 0`かつ`y ≤ 2^k x`なら、
`3y + 1 ≤ 4 · 2^k x`である。
-/
lemma three_mul_add_one_le_four_twoPow_mul
    {x y k : ℕ}
    (hx : 0 < x)
    (hy : y ≤ 2 ^ k * x) :
    3 * y + 1 ≤ 4 * 2 ^ k * x := by
  have hone : 1 ≤ x := hx
  have hpow :
      1 ≤ 2 ^ k :=
    Nat.one_le_pow k 2 (by omega)
  have hxscaled :
      x ≤ 2 ^ k * x := by
    calc
      x = 1 * x := by simp
      _ ≤ 2 ^ k * x :=
        Nat.mul_le_mul_right x hpow
  calc
    3 * y + 1
        ≤ 3 * (2 ^ k * x) + x := by
          omega
    _ ≤ 3 * (2 ^ k * x) + 2 ^ k * x :=
      Nat.add_le_add_left hxscaled _
    _ = 4 * 2 ^ k * x := by
      ring

/--
future-minimumから見た第`k`指数の2冪は、
開始値を掛けた形で`2^(k+2)`以下に抑えられる。
-/
lemma exponent_power_mul_le_position_power
    (O : OddOrbit)
    {n : ℕ}
    (hmin : O.FutureMinimumAt n)
    (k : ℕ) :
    2 ^ O.exponent (n + k) * O.value n ≤
      2 ^ (k + 2) * O.value n := by
  have hstartPos :
      0 < O.value n :=
    O.value_pos n
  have hend :
      O.value n ≤ O.value (n + k + 1) :=
    hmin _ (by omega)
  have hxk :
      O.value (n + k) ≤
        2 ^ k * O.value n :=
    O.segment_value_le hmin k
  have haffine :
      3 * O.value (n + k) + 1 ≤
        4 * 2 ^ k * O.value n :=
    three_mul_add_one_le_four_twoPow_mul
      hstartPos hxk
  calc
    2 ^ O.exponent (n + k) * O.value n
        ≤
          2 ^ O.exponent (n + k) *
            O.value (n + k + 1) :=
      Nat.mul_le_mul_left _ hend
    _ = 3 * O.value (n + k) + 1 := by
      simpa [Nat.add_assoc] using O.step (n + k)
    _ ≤ 4 * 2 ^ k * O.value n :=
      haffine
    _ = 2 ^ (k + 2) * O.value n := by
      rw [
        show k + 2 = k + 1 + 1 by omega,
        pow_succ,
        pow_succ
      ]
      ring

/--
正の自然数`x`について
`2^a x ≤ 2^b x`なら`a ≤ b`である。
-/
lemma exponent_le_of_twoPow_mul_le
    {a b x : ℕ}
    (hx : 0 < x)
    (h :
      2 ^ a * x ≤
        2 ^ b * x) :
    a ≤ b := by
  have hpows :
      2 ^ a ≤ 2 ^ b :=
    Nat.le_of_mul_le_mul_right h hx
  by_contra hnot
  have hba :
      b < a :=
    Nat.lt_of_not_ge hnot
  have hpowlt :
      2 ^ b < 2 ^ a :=
    Nat.pow_lt_pow_right (by omega) hba
  omega

/-- future-minimumから見た第`k`指数は`k+2`以下。 -/
lemma exponent_le_position_add_two
    (O : OddOrbit)
    {n : ℕ}
    (hmin : O.FutureMinimumAt n)
    (k : ℕ) :
    O.exponent (n + k) ≤ k + 2 := by
  have hmain :
      2 ^ O.exponent (n + k) * O.value n ≤
        2 ^ (k + 2) * O.value n :=
    exponent_power_mul_le_position_power
      O hmin k
  exact exponent_le_of_twoPow_mul_le
    (O.value_pos n)
    hmain

end OddOrbit

/-- 有限位置`i`で許される正指数`1,...,i+2`。 -/
abbrev BoundedPositiveExponent (i : ℕ) :=
  {e : Fin (i + 3) // 0 < e.1}

/-- 長さ`m`の指数prefixと、anchorの`2^m`剰余を一つにした有限状態。 -/
@[ext]
structure CompactAnchorState (m : ℕ) where
  exponent : (i : Fin m) → BoundedPositiveExponent i.1
  residue : Fin (2 ^ m)
  deriving Fintype, DecidableEq

namespace CompactAnchorState

/-- 長い有限状態を短い長さへ射影する。 -/
def project {i j : ℕ} (h : i ≤ j)
    (s : CompactAnchorState j) : CompactAnchorState i where
  exponent := fun k =>
    s.exponent ⟨k.1, lt_of_lt_of_le k.2 h⟩
  residue :=
    ⟨s.residue.1 % 2 ^ i,
      Nat.mod_lt _ (Nat.pow_pos (by omega))⟩

@[simp] theorem project_refl (i : ℕ) (s : CompactAnchorState i) :
    project (le_refl i) s = s := by
  cases s with
  | mk e r =>
      apply CompactAnchorState.ext
      · funext k
        rfl
      · apply Fin.ext
        exact Nat.mod_eq_of_lt r.2

@[simp] theorem project_trans
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (s : CompactAnchorState k) :
    project hij (project hjk s) = project (hij.trans hjk) s := by
  apply CompactAnchorState.ext
  · funext a
    rfl
  · apply Fin.ext
    have hdvd : 2 ^ i ∣ 2 ^ j := pow_dvd_pow 2 hij
    exact Nat.mod_mod_of_dvd _ hdvd

/-- 有限状態に保存された指数語。 -/
def word {m : ℕ} (s : CompactAnchorState m) : ExpWord :=
  List.ofFn (fun i : Fin m => (s.exponent i).1.1)

@[simp] theorem word_length {m : ℕ} (s : CompactAnchorState m) :
    s.word.length = m := by simp [word]

/-- 状態の射影は指数語の`take`に一致する。 -/
theorem word_project
    {i j : ℕ} (h : i ≤ j) (s : CompactAnchorState j) :
    (project h s).word = s.word.take i := by
  apply List.ext_get
  · simp only [word_length, List.length_take, left_eq_inf]
    exact h
  · intro k hk₁ hk₂
    simp [word, project]

end CompactAnchorState

/-- future-minimum列の第`j`anchorを長さ`m`で観測した有限状態。 -/
def observedState
    {O : OddOrbit} (S : O.FutureMinimumSequence)
    (j m : ℕ) : CompactAnchorState m where
  exponent := fun i =>
    ⟨⟨O.exponent (S.index j + i.1), by
        have h := O.exponent_le_position_add_two
          (S.futureMinimum j) i.1
        omega⟩,
      O.exponent_pos _⟩
  residue :=
    ⟨O.value (S.index j) % 2 ^ m,
      Nat.mod_lt _ (Nat.pow_pos (by omega))⟩

/--
長さ`m`のsegment wordの第`k`指数は、
開始位置から`k`段目の軌道指数である。
-/
lemma exponent_eq_segmentWord_get
    (O : OddOrbit)
    {n m k : ℕ}
    (hk : k < m) :
    O.exponent (n + k) =
      (O.segmentWord n m).get
        ⟨k, by simpa using hk⟩ := by
  induction m generalizing n k with
  | zero =>
      omega
  | succ m ih =>
      cases k with
      | zero =>
          simp only [add_zero, OddOrbit.segmentWord_succ, List.length_cons,
          Fin.zero_eta, List.get_eq_getElem,
        Fin.coe_ofNat_eq_mod, OddOrbit.segmentWord_length, Nat.zero_mod, List.getElem_cons_zero]
      | succ k =>
          have hk' : k < m := by
            omega
          have htail :=
            ih (n := n + 1) (k := k) hk'
          simp only [OddOrbit.segmentWord, List.get_cons_succ]
          rw [show n + (k + 1) = n + 1 + k by omega]
          exact htail

/-- 観測状態の指数語は実際のsegment wordそのもの。 -/
theorem observedState_word
    {O : OddOrbit}
    (S : O.FutureMinimumSequence)
    (j m : ℕ) :
    (observedState S j m).word =
      O.segmentWord (S.index j) m := by
  apply List.ext_get
  · simp [CompactAnchorState.word]
  · intro k hk₁ hk₂
    have hk : k < m := by
      simpa using hk₂
    have hget :
        O.exponent (S.index j + k) =
          (O.segmentWord (S.index j) m)[k] :=
      exponent_eq_segmentWord_get O hk
    simpa [
      CompactAnchorState.word,
      observedState
    ] using hget

/-- 同じanchorの長い観測を射影すると短い観測になる。 -/
theorem observedState_project
    {O : OddOrbit} (S : O.FutureMinimumSequence)
    {i j : ℕ} (h : i ≤ j) (n : ℕ) :
    CompactAnchorState.project h (observedState S n j) =
      observedState S n i := by
  apply CompactAnchorState.ext
  · funext k
    rfl
  · apply Fin.ext
    have hdvd : 2 ^ i ∣ 2 ^ j := pow_dvd_pow 2 h
    exact Nat.mod_mod_of_dvd _ hdvd

/-- 長さ`m`の観測状態のうち、無限回現れるもの。 -/
def FrequentAnchorState
    {O : OddOrbit} (S : O.FutureMinimumSequence) (m : ℕ) :=
  {s : CompactAnchorState m //
    Set.Infinite {j : ℕ | observedState S j m = s}}

noncomputable instance frequentAnchorStateNonempty
    {O : OddOrbit} (S : O.FutureMinimumSequence) (m : ℕ) :
    Nonempty (FrequentAnchorState S m) := by
  obtain ⟨s, hs⟩ :=
    Finite.exists_infinite_fiber (fun j : ℕ => observedState S j m)
  exact ⟨⟨s, by
    apply Set.infinite_coe_iff.mp
    simpa [Set.preimage, Set.mem_singleton_iff] using hs
  ⟩⟩

/-- 無限頻出状態の射影。 -/
def frequentProject
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    {i j : ℕ} (h : i ≤ j)
    (s : FrequentAnchorState S j) : FrequentAnchorState S i := by
  refine ⟨CompactAnchorState.project h s.1, ?_⟩
  apply s.2.mono
  intro n hn
  have hp := congrArg (CompactAnchorState.project h) hn
  simpa [observedState_project S h n] using hp

/-- 頻出anchor状態も有限である。 -/
instance frequentAnchorStateFinite
    {O : OddOrbit}
    (S : O.FutureMinimumSequence)
    (m : ℕ) :
    Finite (FrequentAnchorState S m) := by
  exact Finite.of_injective
    (fun s : FrequentAnchorState S m =>
      (s.1 : CompactAnchorState m))
    (by
      intro a b hab
      exact Subtype.ext hab)

/-- Kőnigの無限補題で互いに整合する無限頻出状態列を取る。 -/
theorem exists_coherent_frequent_states
    {O : OddOrbit} (S : O.FutureMinimumSequence) :
    ∃ f : (m : ℕ) → FrequentAnchorState S m,
      ∀ ⦃i j : ℕ⦄ (h : i ≤ j),
        frequentProject h (f j) = f i := by
  classical
  letI (m : ℕ) : Nonempty (FrequentAnchorState S m) :=
    frequentAnchorStateNonempty S m
  apply exists_seq_forall_proj_of_forall_finite
    (π := fun {_ _} h => frequentProject h)
  · intro i a
    apply Subtype.ext
    exact CompactAnchorState.project_refl i a.1
  · intro i j k hij hjk a
    apply Subtype.ext
    exact CompactAnchorState.project_trans hij hjk a.1
  · intro i a
    exact Set.finite_univ.subset (Set.subset_univ _)

/-- 無限集合は任意の自然数より大きい要素を持つ。 -/
lemma infinite_set_exists_gt
    {s : Set ℕ} (hs : s.Infinite) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ n ∈ s := by
  by_contra h
  push Not at h
  have hsub : s ⊆ Set.Iic N := by
    intro n hn
    change n ≤ N
    by_contra hnle
    have hgt : N < n := Nat.lt_of_not_ge hnle
    exact (h n hgt) hn
  exact hs ((Set.finite_Iic N).subset hsub)

/-- 整合状態`f m`を実現するanchorを狭義単調に選ぶ。 -/
noncomputable def occurrenceSubsequence
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m) : ℕ → ℕ
  | 0 => Classical.choose (infinite_set_exists_gt (f 0).2 0)
  | m + 1 =>
      Classical.choose
        (infinite_set_exists_gt (f (m + 1)).2
          (occurrenceSubsequence f m))

lemma occurrenceSubsequence_spec
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (m : ℕ) :
    observedState S (occurrenceSubsequence f m) m = (f m).1 := by
  cases m with
  | zero =>
      exact (Classical.choose_spec
        (infinite_set_exists_gt (f 0).2 0)).2
  | succ m =>
      exact (Classical.choose_spec
        (infinite_set_exists_gt (f (m + 1)).2
          (occurrenceSubsequence f m))).2

lemma occurrenceSubsequence_lt_succ
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (m : ℕ) :
    occurrenceSubsequence f m < occurrenceSubsequence f (m + 1) := by
  exact (Classical.choose_spec
    (infinite_set_exists_gt (f (m + 1)).2
      (occurrenceSubsequence f m))).1

lemma occurrenceSubsequence_strict
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m) :
    StrictMono (occurrenceSubsequence f) :=
  strictMono_nat_of_lt_succ (occurrenceSubsequence_lt_succ f)

lemma occurrenceSubsequence_ge_id
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (m : ℕ) :
    m ≤ occurrenceSubsequence f m := by
  induction m with
  | zero => omega
  | succ m ih =>
      have h := occurrenceSubsequence_lt_succ f m
      omega

/-- 元future-minimum列を狭義単調な無限部分列へ制限する。 -/
noncomputable def extractedMinima
    {O : OddOrbit} (S : O.FutureMinimumSequence)
    (f : (m : ℕ) → FrequentAnchorState S m) :
    O.FutureMinimumSequence where
  index := fun m => S.index (occurrenceSubsequence f m)
  index_strict := S.index_strict.comp (occurrenceSubsequence_strict f)
  futureMinimum := fun m => S.futureMinimum _
  value_strict := S.value_strict.comp (occurrenceSubsequence_strict f)
  eventually_large := by
    intro M J
    obtain ⟨k, hkJ, hkM⟩ := S.eventually_large M (occurrenceSubsequence f J)
    let j := max J k
    refine ⟨j, le_max_left _ _, ?_⟩
    have hkselect : k ≤ occurrenceSubsequence f j := by
      exact le_trans (le_max_right _ _) (occurrenceSubsequence_ge_id f j)
    have hval :
        O.value (S.index k) ≤
          O.value (S.index (occurrenceSubsequence f j)) := by
      exact (S.value_strict.monotone hkselect)
    omega

/-- 整合状態列が与える2進shadow。 -/
def coherentShadowOfStates
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (hf : ∀ ⦃i j : ℕ⦄ (h : i ≤ j),
      frequentProject h (f j) = f i) :
    CoherentTwoAdicShadow where
  residue := fun r => ((f r).1.residue).1
  residue_lt := fun r => ((f r).1.residue).2
  compatible := by
    intro r
    have h := congrArg
      (fun s : FrequentAnchorState S r => s.1.residue.1)
      (hf (Nat.le_succ r))
    simpa [frequentProject, CompactAnchorState.project] using h

/-- 整合状態列が与える第`n`極限指数。 -/
def coherentLimitExponent
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (n : ℕ) : ℕ :=
  (((f (n + 1)).1.exponent ⟨n, by omega⟩).1).1

lemma coherentLimitExponent_pos
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (n : ℕ) :
    0 < coherentLimitExponent f n :=
  (((f (n + 1)).1.exponent ⟨n, by omega⟩).2)

/-- 長さ`m`状態の各座標は同じ極限指数を保持する。 -/
theorem coherentLimitExponent_at
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (hf : ∀ ⦃i j : ℕ⦄ (h : i ≤ j),
      frequentProject h (f j) = f i)
    {m : ℕ} (k : Fin m) :
    coherentLimitExponent f k.1 =
      (((f m).1.exponent k).1).1 := by
  have hkm : k.1 + 1 ≤ m := by omega
  have hs := congrArg Subtype.val (hf hkm)
  have he := congrArg
    (fun s : CompactAnchorState (k.1 + 1) =>
      (((s.exponent ⟨k.1, by omega⟩).1).1)) hs
  simpa [coherentLimitExponent, frequentProject,
    CompactAnchorState.project] using he.symm

/-- 長さ`m`の整合状態語は極限指数列のprefixである。 -/
theorem prefixWord_coherentLimitExponent
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (hf : ∀ ⦃i j : ℕ⦄ (h : i ≤ j),
      frequentProject h (f j) = f i)
    (m : ℕ) :
    prefixWord (coherentLimitExponent f) m = (f m).1.word := by
  rw [prefixWord_eq_ofFn]
  unfold CompactAnchorState.word
  rw [List.ofFn_inj]
  funext k
  exact coherentLimitExponent_at f hf k

/-- 抽出部分列上では各固定長の指数語が最終的に極限語へ一致する。 -/
theorem extracted_prefix_stabilizes
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (hf : ∀ ⦃i j : ℕ⦄ (h : i ≤ j),
      frequentProject h (f j) = f i) :
    ∀ m : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      O.segmentWord ((extractedMinima S f).index j) m =
        prefixWord (coherentLimitExponent f) m := by
  intro m
  refine ⟨m, ?_⟩
  intro j hj
  have hobs := occurrenceSubsequence_spec f j
  have hproj := congrArg (CompactAnchorState.project hj) hobs
  have hcoh := congrArg Subtype.val (hf hj)
  have hstate :
      observedState S (occurrenceSubsequence f j) m = (f m).1 := by
    calc
      observedState S (occurrenceSubsequence f j) m
          = CompactAnchorState.project hj
              (observedState S (occurrenceSubsequence f j) j) := by
                symm
                exact observedState_project S hj _
      _ = CompactAnchorState.project hj (f j).1 := hproj
      _ = (f m).1 := hcoh
  calc
    O.segmentWord ((extractedMinima S f).index j) m
        = (observedState S (occurrenceSubsequence f j) m).word := by
            symm
            exact observedState_word S _ _
    _ = (f m).1.word := congrArg CompactAnchorState.word hstate
    _ = prefixWord (coherentLimitExponent f) m :=
          (prefixWord_coherentLimitExponent f hf m).symm

/-- 抽出部分列のanchorは整合shadowへ2進収束する。 -/
theorem extracted_shadow_convergence
    {O : OddOrbit} {S : O.FutureMinimumSequence}
    (f : (m : ℕ) → FrequentAnchorState S m)
    (hf : ∀ ⦃i j : ℕ⦄ (h : i ≤ j),
      frequentProject h (f j) = f i) :
    ConvergesToShadow
      (fun j => O.value ((extractedMinima S f).index j))
      (coherentShadowOfStates f hf) := by
  intro r
  refine ⟨r, ?_⟩
  intro j hj
  have hobs := occurrenceSubsequence_spec f j
  have hp := congrArg (CompactAnchorState.project hj) hobs
  have hc := congrArg Subtype.val (hf hj)
  have hs :
      observedState S (occurrenceSubsequence f j) r = (f r).1 := by
    calc
      observedState S (occurrenceSubsequence f j) r
          = CompactAnchorState.project hj
              (observedState S (occurrenceSubsequence f j) j) := by
                symm
                exact observedState_project S hj _
      _ = CompactAnchorState.project hj (f j).1 := hp
      _ = (f r).1 := hc
  have hr := congrArg (fun s : CompactAnchorState r => s.residue.1) hs
  simpa [extractedMinima, observedState, coherentShadowOfStates] using hr

/-- 非有界軌道からmoving-limitデータを実際に構成する。 -/
theorem movingLimitData_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (MovingLimitData O) := by
  classical
  let S := O.futureMinimumSequenceOfUnbounded hU
  obtain ⟨f, hf⟩ := exists_coherent_frequent_states S
  let S' := extractedMinima S f
  let ξ := coherentShadowOfStates f hf
  refine ⟨{
    minima := S'
    shadow := ξ
    shadow_convergence := extracted_shadow_convergence f hf
    limitExponent := coherentLimitExponent f
    limitExponent_pos := coherentLimitExponent_pos f
    prefix_stabilizes := extracted_prefix_stabilizes f hf
  }⟩

/-- 非有界軌道からmoving-limitデータを抽出できるという第一bridge。 -/
def MovingCompactnessPrinciple : Prop :=
  ∀ O : OddOrbit, O.Unbounded → Nonempty (MovingLimitData O)

/-- 第一bridgeの完全な証明。 -/
theorem movingCompactnessPrinciple : MovingCompactnessPrinciple := by
  intro O hU
  exact movingLimitData_of_unbounded O hU

end CollatzSecondLayer
