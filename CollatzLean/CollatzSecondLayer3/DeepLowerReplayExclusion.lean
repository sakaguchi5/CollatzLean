import CollatzLean.CollatzSecondLayer3.FutureMinimumDeepLowerReplay
import CollatzLean.CollatzOrbitCore.PeriodicExponent

import Mathlib.Data.Finset.Basic

/-!
# 生成履歴付きdeep lower-replay towerの排除

全十分大きなwindow長を同じanchorから生成する履歴を使う。

deep lower replayは各terminal値に指数的な下界を与えるため、
固定した時刻より前にterminalが残り続けることはできない。
一方、terminal以前のcapture / synchronized履歴は、距離`q`だけ離れた
指数を点ごとに非増加にする。全十分大きな`q`を走らせると、指数tailは
最終的に定数となる。

定数が1ならexpandingな周期指数tailとなり、定数が2以上なら値tailが
非増加となる。どちらも非有界軌道に反する。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- `n < 2^(n+1)`。terminal位置の有限prefix上界を超えるために使う。 -/
private theorem nat_lt_twoPow_succ (n : ℕ) :
    n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) :=
        Nat.pow_pos (by omega)
      omega

/-- anchorから`t`時刻までの値を全て支配する有限上界。 -/
private def prefixValueBound
    (O : OddOrbit) (anchor t : ℕ) : ℕ :=
  Finset.sum (Finset.range (t + 1))
    (fun k => O.value (anchor + k))

/-- prefix内の各値は`prefixValueBound`以下。 -/
private theorem value_le_prefixValueBound
    (O : OddOrbit) (anchor t s : ℕ)
    (hs : s ≤ t) :
    O.value (anchor + s) ≤ prefixValueBound O anchor t := by
  unfold prefixValueBound
  exact
    Finset.single_le_sum
      (fun k (_hk : k ∈ Finset.range (t + 1)) =>
        Nat.zero_le (O.value (anchor + k)))
      (Finset.mem_range.mpr (by omega))

namespace CoherentDeepLowerReplayTowerData

/-- deep lower replayの開始値は対応するresidue modulus以上。 -/
theorem residueModulus_le_startValue
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (j : ℕ) :
    residueModulus
        (O.segmentWord (R.start j) (R.length j)) ≤
      O.value (R.start j) := by
  have hstart := (R.deep j).lowerReplay.start_step
  omega

/-- deep条件から、terminal開始値は`2^(length+1)`以上。 -/
theorem twoPow_length_succ_le_startValue
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (j : ℕ) :
    2 ^ (R.length j + 1) ≤ O.value (R.start j) := by
  exact le_trans
    (R.deep j).modulus_deep
    (R.residueModulus_le_startValue j)

/--
任意の固定時刻`t`に対し、十分大きな全windowのterminal timeは`t`より後ろにある。
-/
theorem terminalTime_eventually_gt
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (t : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → t < R.terminalTime j := by
  let B := prefixValueBound O R.anchor t
  refine ⟨B + 1, ?_⟩
  intro j hj
  by_contra hnot
  have hterminalLe : R.terminalTime j ≤ t :=
    Nat.le_of_not_gt hnot
  have hvalueLe : O.value (R.start j) ≤ B := by
    simpa [CoherentDeepLowerReplayTowerData.start] using
      value_le_prefixValueBound
        O R.anchor t (R.terminalTime j) hterminalLe
  have hpowLe :
      2 ^ (R.length j + 1) ≤ O.value (R.start j) :=
    R.twoPow_length_succ_le_startValue j
  have hBltBase : B < 2 ^ (B + 1) :=
    nat_lt_twoPow_succ B
  have hexponentLe : B + 1 ≤ R.length j + 1 := by
    unfold CoherentDeepLowerReplayTowerData.length futureTailLength
    omega
  have hBlt : B < 2 ^ (R.length j + 1) :=
    lt_of_lt_of_le hBltBase
      (Nat.pow_le_pow_right (by omega) hexponentLe)
  omega

/--
terminal以前ではcaptureが指数を真に下げ、synchronizedが指数を保存するため、
距離`length j`だけ先の指数は現在の指数以下。
-/
theorem exponent_shift_le_of_before
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    {j t : ℕ}
    (ht : t < R.terminalTime j) :
    O.exponent (R.anchor + t + R.length j) ≤
      O.exponent (R.anchor + t) := by
  rcases R.before j t ht with ⟨C | S⟩
  · exact Nat.le_of_lt C.upperExponent_lt_lowerExponent
  · exact S.upperExponent_eq_lower.le

end CoherentDeepLowerReplayTowerData

/-- anchor以後に現れる指数値は少なくとも一つ存在する。 -/
private theorem exists_tail_exponent
    (O : OddOrbit) (anchor : ℕ) :
    ∃ e : ℕ, ∃ t : ℕ, O.exponent (anchor + t) = e :=
  ⟨O.exponent anchor, 0, by simp⟩

/-- anchor以後に現れる最小指数。 -/
private noncomputable def tailExponentMinimum
    (O : OddOrbit) (anchor : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_tail_exponent O anchor)

/-- tailExponentMinimumはanchor以後に実際に現れる。 -/
private theorem tailExponentMinimum_spec
    (O : OddOrbit) (anchor : ℕ) :
    ∃ t : ℕ,
      O.exponent (anchor + t) =
        tailExponentMinimum O anchor := by
  classical
  exact Nat.find_spec (exists_tail_exponent O anchor)

/-- anchor以後に現れる任意の指数はtailExponentMinimum以上。 -/
private theorem tailExponentMinimum_le
    (O : OddOrbit) (anchor n : ℕ)
    (hn : ∃ t : ℕ, O.exponent (anchor + t) = n) :
    tailExponentMinimum O anchor ≤ n := by
  classical
  exact Nat.find_min' (exists_tail_exponent O anchor) hn

namespace CoherentDeepLowerReplayTowerData

/--
指数が最小値を取るtail位置を固定すると、
その位置がterminalより前にある各tower windowの平行移動先でも
指数は同じ最小値を取る。
-/
private theorem exponent_eq_tailMinimum_of_before
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    {t j : ℕ}
    (ht :
      O.exponent (R.anchor + t) =
        tailExponentMinimum O R.anchor)
    (hbefore : t < R.terminalTime j) :
    O.exponent (R.anchor + t + R.length j) =
      tailExponentMinimum O R.anchor := by
  have hshift :=
    R.exponent_shift_le_of_before hbefore
  have hupper :
      O.exponent (R.anchor + t + R.length j) ≤
        tailExponentMinimum O R.anchor := by
    calc
      O.exponent (R.anchor + t + R.length j)
          ≤ O.exponent (R.anchor + t) := hshift
      _ = tailExponentMinimum O R.anchor := ht
  have hlower :
      tailExponentMinimum O R.anchor ≤
        O.exponent (R.anchor + t + R.length j) := by
    have hmin :=
      tailExponentMinimum_le
        O
        R.anchor
        (O.exponent (R.anchor + (t + R.length j)))
        ⟨t + R.length j, rfl⟩
    simpa [Nat.add_assoc] using hmin
  exact Nat.le_antisymm hupper hlower


/--
指数tailの定数性を開始するための基準添字。

`t`は最小指数が現れるoffsetであり、
この位置以後はtowerの長さ`cutoff + j + 1`によって
連続するすべての添字を表せる。
-/
private def exponentConstancyBase
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (t : ℕ) : ℕ :=
  R.anchor + t + R.cutoff + 1


/--
terminal timeが十分大きくなるtower添字の閾値を加えた、
指数定数性の最終閾値。
-/
private def exponentConstancyThreshold
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (t J : ℕ) : ℕ :=
  exponentConstancyBase R t + J


/--
最終閾値以後の添字から得られるtower添字は、
terminal timeの閾値`J`以後にある。
-/
private theorem exponentConstancy_index_bounds
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (t J n : ℕ)
    (hn : exponentConstancyThreshold R t J ≤ n) :
    exponentConstancyBase R t ≤ n ∧
      J ≤ n - exponentConstancyBase R t := by
  change exponentConstancyBase R t + J ≤ n at hn
  omega


/--
base以後の任意の添字は、
`anchor + t`にtowerの標準長さを加えた形で表せる。
-/
private theorem exponentConstancy_index_eq
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O)
    (t n : ℕ)
    (hbase : exponentConstancyBase R t ≤ n) :
    n =
      R.anchor + t +
        R.length (n - exponentConstancyBase R t) := by
  have hsub :
      n - exponentConstancyBase R t +
          exponentConstancyBase R t =
        n :=
    Nat.sub_add_cancel hbase
  calc
    n =
        n - exponentConstancyBase R t +
          exponentConstancyBase R t := hsub.symm
    _ =
        R.anchor + t +
          R.length
            (n - exponentConstancyBase R t) := by
      unfold exponentConstancyBase
      unfold CoherentDeepLowerReplayTowerData.length
      unfold futureTailLength
      ring


/--
tail exponent minimumは正。
-/
private theorem tailExponentMinimum_pos
    (O : OddOrbit)
    (anchor : ℕ) :
    0 < tailExponentMinimum O anchor := by
  classical
  obtain ⟨t, ht⟩ :=
    tailExponentMinimum_spec O anchor
  rw [← ht]
  exact O.exponent_pos (anchor + t)


/--
coherent deep lower-replay towerが存在すると、元軌道の指数tailは最終的に定数。
-/
theorem exponent_eventually_constant
    {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O) :
    ∃ N m : ℕ,
      0 < m ∧
      ∀ n : ℕ, N ≤ n → O.exponent n = m := by
  classical
  let m : ℕ :=
    tailExponentMinimum O R.anchor
  obtain ⟨t₀, ht₀⟩ :=
    tailExponentMinimum_spec O R.anchor
  obtain ⟨J, hJ⟩ :=
    R.terminalTime_eventually_gt t₀
  let N : ℕ :=
    exponentConstancyThreshold R t₀ J
  refine ⟨N, m, ?_, ?_⟩
  · simpa [m] using
      tailExponentMinimum_pos O R.anchor
  · intro n hn
    have hn' :
        exponentConstancyThreshold R t₀ J ≤ n := by
      simpa [N] using hn
    obtain ⟨hbase, hj⟩ :=
      exponentConstancy_index_bounds
        R t₀ J n hn'
    let j : ℕ :=
      n - exponentConstancyBase R t₀
    have hj' : J ≤ j := by
      simpa [j] using hj
    have hterminal :
        t₀ < R.terminalTime j :=
      hJ j hj'
    have heq :
        O.exponent (R.anchor + t₀ + R.length j) =
          tailExponentMinimum O R.anchor :=
      exponent_eq_tailMinimum_of_before
        R ht₀ hterminal
    have hindex :
        n = R.anchor + t₀ + R.length j := by
      simpa [j] using
        exponentConstancy_index_eq
          R t₀ n hbase
    rw [hindex]
    simpa [m] using heq

end CoherentDeepLowerReplayTowerData

/-- 指数が2以上ならodd-only一段で値は増加しない。 -/
private theorem value_succ_le_of_exponent_two_le
    (O : OddOrbit) {n m : ℕ}
    (hm : 2 ≤ m)
    (hexponent : O.exponent n = m) :
    O.value (n + 1) ≤ O.value n := by
  have hpow : 4 ≤ 2 ^ m := by
    simpa using
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hm)
  have hstep := O.step n
  rw [hexponent] at hstep
  have hscaled :
      4 * O.value (n + 1) ≤ 4 * O.value n := by
    calc
      4 * O.value (n + 1)
          ≤ 2 ^ m * O.value (n + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * O.value n + 1 := hstep
      _ ≤ 4 * O.value n := by
        have hpos := O.value_pos n
        omega
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- 非有界odd-only軌道の指数tailは定数になれない。 -/
private theorem no_eventually_constant_exponent_tail
    (O : OddOrbit)
    (hU : O.Unbounded)
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
          calc
            O.value (N + (t + 1))
                = O.value ((N + t) + 1) := by
                    congr 1
            _ ≤ O.value (N + t) := hs
            _ ≤ O.value N := ih
    obtain ⟨K, hK⟩ :=
      O.escapesToInfinity_of_unbounded hU (O.value N)
    let n : ℕ := max K N
    have hnK : K ≤ n := by
      dsimp [n]
      exact le_max_left K N
    have hnN : N ≤ n := by
      dsimp [n]
      exact le_max_right K N
    have hlarge : O.value N < O.value n :=
      hK n hnK
    let t : ℕ := n - N
    have hnEq : n = N + t := by
      dsimp [t]
      omega
    have hle := htailLe t
    rw [← hnEq] at hle
    omega

/--
非有界軌道上のcoherent deep lower-replay towerは存在しない。
-/
theorem no_coherentDeepLowerReplayTower_of_unbounded
    {O : OddOrbit}
    (hU : O.Unbounded)
    (R : CoherentDeepLowerReplayTowerData O) :
    False := by
  obtain ⟨N, m, hmPos, hconstant⟩ :=
    R.exponent_eventually_constant
  exact no_eventually_constant_exponent_tail
    O hU hmPos hconstant

/--
future-minimum生成履歴を完全保存したdeep lower-replay towerは存在しない。
-/
theorem no_futureMinimumDeepLowerReplayTower
    {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) :
    False := by
  exact no_coherentDeepLowerReplayTower_of_unbounded
    R.unbounded R.toCoherent

end CollatzSecondLayer3
