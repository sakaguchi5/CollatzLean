import CollatzLean.CollatzSecondLayer3.ConstantTerminalObstruction
import CollatzLean.CollatzOrbitCore.PeriodicExponent

/-!
# terminal escapeから指数tail定数化、非有界性との矛盾

Constant terminal排除により全長さのterminal timeが任意の固定時刻を越えるとする。
anchor以後に現れる最小exponentを一つ固定し、その位置を十分大きい全windowの
terminal以前に置く。captureは上側exponentを真に下げ、synchronizedは保存するため、
距離`q + 1`先のexponentは最小値以下になる。tail最小性と合わせて等号となる。

ここでは全ての長さ`q + 1`を直接走らせるため、deep lower-replay tower版にあった
標準長さ列の添字復元は不要であり、exponent tailの全点を直接覆える。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumAllLengthTerminalData

/-- terminal以前では距離`q + 1`先のexponentは現在以下。 -/
theorem exponent_shift_le_of_before
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    {q t : ℕ}
    (ht : t < A.terminalTime q) :
    O.exponent (A.anchor + t + A.length q) ≤
      O.exponent (A.anchor + t) := by
  rcases A.before q t ht with ⟨C | S⟩
  · exact Nat.le_of_lt C.upperExponent_lt_lowerExponent
  · exact S.upperExponent_eq_lower.le

/-- anchor以後に現れるexponent値は非空。 -/
private theorem exists_tail_exponent
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O) :
    ∃ e : ℕ, ∃ t : ℕ, O.exponent (A.anchor + t) = e :=
  ⟨O.exponent A.anchor, 0, by simp⟩

/-- anchor以後に実際に現れる最小exponent。 -/
noncomputable def tailExponentMinimum
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O) : ℕ := by
  classical
  exact Nat.find (A.exists_tail_exponent)

/-- tail最小exponentは実際のoffsetで達成される。 -/
theorem tailExponentMinimum_spec
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O) :
    ∃ t : ℕ,
      O.exponent (A.anchor + t) = A.tailExponentMinimum := by
  classical
  exact Nat.find_spec (A.exists_tail_exponent)

/-- anchor以後に現れる任意のexponentはtail最小値以上。 -/
theorem tailExponentMinimum_le
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (n : ℕ)
    (hn : ∃ t : ℕ, O.exponent (A.anchor + t) = n) :
    A.tailExponentMinimum ≤ n := by
  classical
  exact Nat.find_min' (A.exists_tail_exponent) hn

/-- tail最小exponentは正。 -/
theorem tailExponentMinimum_pos
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O) :
    0 < A.tailExponentMinimum := by
  obtain ⟨t, ht⟩ := A.tailExponentMinimum_spec
  rw [← ht]
  exact O.exponent_pos (A.anchor + t)

/--
最小exponent位置がterminal以前なら、距離`q + 1`先でも同じ最小値を取る。
-/
theorem exponent_eq_tailMinimum_of_before
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    {t q : ℕ}
    (ht : O.exponent (A.anchor + t) = A.tailExponentMinimum)
    (hbefore : t < A.terminalTime q) :
    O.exponent (A.anchor + t + A.length q) = A.tailExponentMinimum := by
  have hshift := A.exponent_shift_le_of_before hbefore
  have hupper :
      O.exponent (A.anchor + t + A.length q) ≤ A.tailExponentMinimum := by
    calc
      O.exponent (A.anchor + t + A.length q)
          ≤ O.exponent (A.anchor + t) := hshift
      _ = A.tailExponentMinimum := ht
  have hlower :
      A.tailExponentMinimum ≤
        O.exponent (A.anchor + t + A.length q) := by
    have hmin :=
      A.tailExponentMinimum_le
        (O.exponent (A.anchor + (t + A.length q)))
        ⟨t + A.length q, rfl⟩
    simpa [Nat.add_assoc] using hmin
  exact Nat.le_antisymm hupper hlower

/--
terminal timeが全固定時刻から逃げるなら、軌道のexponent tailは最終的に定数。
全長さを使うので、十分後の任意位置`n`に対して
`q = n - (anchor + t₀ + 1)`を直接選べる。
-/
theorem exponent_eventually_constant_of_terminalTimeEscapes
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (hEscape : A.TerminalTimeEscapes) :
    ∃ N m : ℕ,
      0 < m ∧
      ∀ n : ℕ, N ≤ n → O.exponent n = m := by
  classical
  let m := A.tailExponentMinimum
  obtain ⟨t₀, ht₀⟩ := A.tailExponentMinimum_spec
  obtain ⟨Q, hQ⟩ := hEscape t₀
  let N := A.anchor + t₀ + Q + 1
  refine ⟨N, m, ?_, ?_⟩
  · simpa [m] using A.tailExponentMinimum_pos
  · intro n hn
    let q := n - (A.anchor + t₀ + 1)
    have hq : Q ≤ q := by
      dsimp [N, q] at hn ⊢
      omega
    have hterminal : t₀ < A.terminalTime q :=
      hQ q hq
    have heq :
        O.exponent (A.anchor + t₀ + A.length q) =
          A.tailExponentMinimum :=
      A.exponent_eq_tailMinimum_of_before ht₀ hterminal
    have hindex : n = A.anchor + t₀ + A.length q := by
      dsimp [q]
      unfold length
      dsimp [N] at hn
      omega
    rw [hindex]
    simpa [m] using heq

/-- exponentが2以上ならodd-only一段で値は非増加。 -/
private theorem value_succ_le_of_exponent_two_le
    (O : OddOrbit)
    {n m : ℕ}
    (hm : 2 ≤ m)
    (hexponent : O.exponent n = m) :
    O.value (n + 1) ≤ O.value n := by
  have hpow : 4 ≤ 2 ^ m := by
    simpa using
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hm)
  have hstep := O.step n
  rw [hexponent] at hstep
  have hscaled : 4 * O.value (n + 1) ≤ 4 * O.value n := by
    calc
      4 * O.value (n + 1)
          ≤ 2 ^ m * O.value (n + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * O.value n + 1 := hstep
      _ ≤ 4 * O.value n := by
        have hpos := O.value_pos n
        omega
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- 非有界odd-only軌道は最終定数exponent tailを持てない。 -/
theorem no_eventually_constant_exponent_tail
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    {N m : ℕ}
    (hmPos : 0 < m)
    (hconstant : ∀ n : ℕ, N ≤ n → O.exponent n = m) :
    False := by
  by_cases hmOne : m = 1
  · have hperiod : ∀ t : ℕ,
        O.exponent (N + t + 1) = O.exponent (N + t) := by
      intro t
      rw [hconstant (N + t + 1) (by omega)]
      rw [hconstant (N + t) (by omega)]
    have hword : O.segmentWord N 1 = [1] := by
      simp [hmOne, hconstant N le_rfl]
    have hexpanding : Expanding (O.segmentWord N 1) := by
      rw [hword]
      norm_num [Expanding, oddSteps, twoSteps]
    exact O.no_expanding_periodic_exponent_tail
      (q := 1) hperiod hexpanding
  · have hmTwo : 2 ≤ m := by omega
    have hstepLe : ∀ n : ℕ, N ≤ n →
        O.value (n + 1) ≤ O.value n := by
      intro n hn
      exact value_succ_le_of_exponent_two_le
        O hmTwo (hconstant n hn)
    have htailLe : ∀ t : ℕ,
        O.value (N + t) ≤ O.value N := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          have hs := hstepLe (N + t) (by omega)
          have hindex : N + (t + 1) = N + t + 1 := by omega
          rw [hindex]
          exact le_trans hs ih
    have hescape :=
      O.escapesToInfinity_of_unbounded A.unbounded (O.value N)
    obtain ⟨J, hJ⟩ := hescape
    have hgt := hJ (N + J) (by omega)
    have hle : O.value (N + J) ≤ O.value N :=
      htailLe J
    omega

/-- terminal time escapeは非有界性に矛盾する。 -/
theorem impossible_of_terminalTimeEscapes
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (hEscape : A.TerminalTimeEscapes) :
    False := by
  obtain ⟨N, m, hmPos, hconstant⟩ :=
    A.exponent_eventually_constant_of_terminalTimeEscapes hEscape
  exact A.no_eventually_constant_exponent_tail hmPos hconstant

/--
Constant terminal Special C3 familyが存在しない全長さ系は不可能。
これがConstant排除から発散反例排除へ接続する中心定理。
-/
theorem impossible_of_no_constantTerminal
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (hNoConstant :
      ¬ Nonempty (ConstantTerminalSpecialC3FamilyData A)) :
    False := by
  exact A.impossible_of_terminalTimeEscapes
    (A.terminalTime_escapes_of_no_constant hNoConstant)

end FutureMinimumAllLengthTerminalData
end CollatzSecondLayer3
