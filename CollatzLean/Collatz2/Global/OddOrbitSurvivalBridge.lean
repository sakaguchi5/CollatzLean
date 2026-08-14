import CollatzLean.Collatz2.Global.InfiniteSurvival
import CollatzLean.Collatz2.Orbit.OddOrbit

/-!
# Collatz2: OddOrbit から NestedSurvivalChain への橋

任意の normalized odd-only `OddOrbit` には、その値域の最小値が存在する。
その最小値を `x`、最初の最小値到達位置を `i` とし、

  `word n     = O.segment i (n + 1)`
  `endpoint n = O.value (i + (n + 1))`

と置く。

最小性により future の全 actual boundary は `x` 以上であり、
各 exponent は正なので residue modulus は無限に深くなる。
従ってこの minimum tail は `NestedSurvivalChain x` を自然に与える。

このファイルは `OddOrbit` と `InfiniteSurvival` の abstract chain を結ぶだけで、
新しい trajectory-specific data は導入しない。
-/

namespace Collatz2
namespace OddOrbit

/-- 軌道値の中に少なくとも一つ自然数値が存在する。 -/
private theorem exists_orbit_value (O : OddOrbit) :
    ∃ a : ℕ, ∃ n : ℕ, O.value n = a := by
  exact ⟨O.value 0, 0, rfl⟩

/--
軌道全体の値域の最小値。
`Nat.find` により値そのものを最小化する。
-/
noncomputable def globalMinimumValue (O : OddOrbit) : ℕ := by
  classical
  exact Nat.find (exists_orbit_value O)

/-- global minimum は実際に軌道上で達成される。 -/
theorem exists_value_eq_globalMinimumValue
    (O : OddOrbit) :
    ∃ n : ℕ, O.value n = O.globalMinimumValue := by
  classical
  exact Nat.find_spec (exists_orbit_value O)

/-- global minimum は任意の軌道値以下。 -/
theorem globalMinimumValue_le_value
    (O : OddOrbit)
    (n : ℕ) :
    O.globalMinimumValue ≤ O.value n := by
  classical
  exact Nat.find_min' (exists_orbit_value O) ⟨n, rfl⟩

/-- global minimum が最初に現れる index。 -/
noncomputable def globalMinimumIndex (O : OddOrbit) : ℕ := by
  classical
  exact Nat.find (O.exists_value_eq_globalMinimumValue)

/-- `globalMinimumIndex` では値が exact に global minimum。 -/
theorem value_globalMinimumIndex
    (O : OddOrbit) :
    O.value O.globalMinimumIndex = O.globalMinimumValue := by
  classical
  exact Nat.find_spec (O.exists_value_eq_globalMinimumValue)

/-- global minimum は正。 -/
theorem globalMinimumValue_pos
    (O : OddOrbit) :
    0 < O.globalMinimumValue := by
  rw [← O.value_globalMinimumIndex]
  exact O.value_pos O.globalMinimumIndex

/-- global minimum は odd。 -/
theorem globalMinimumValue_odd
    (O : OddOrbit) :
    Odd O.globalMinimumValue := by
  rw [← O.value_globalMinimumIndex]
  exact O.value_odd O.globalMinimumIndex

/-- valid word では各 exponent が1以上なので、word 長は総2指数以下。 -/
private theorem length_le_twoSteps_of_valid
    {w : Word}
    (hvalid : w.Valid) :
    w.length ≤ w.twoSteps := by
  induction w with
  | nil =>
      simp [Word.twoSteps]
  | cons e w ih =>
      have he : 0 < e := hvalid e (by simp)
      have htail : Word.Valid w := by
        intro a ha
        exact hvalid a (by simp [ha])
      have hih := ih htail
      simp only [List.length_cons, Word.twoSteps_cons]
      omega

/-- elementary growth bound `n+1 ≤ 2^n`。 -/
private theorem succ_le_two_pow
    (n : ℕ) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [pow_succ]
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      omega

/--
同じ word と同じ start を持つ二つの affine realization は endpoint が一意。
minimum-tail の arbitrary prefix run を actual orbit boundary と同定する補助定理。
-/
private theorem realizes_endpoint_unique
    {w : Word} {x y z : ℕ}
    (hy : Word.Realizes w x y)
    (hz : Word.Realizes w x z) :
    y = z := by
  have hyEq := (Word.realizes_iff w x y).1 hy
  have hzEq := (Word.realizes_iff w x z).1 hz
  have hmul :
      2 ^ w.twoSteps * y = 2 ^ w.twoSteps * z := by
    calc
      2 ^ w.twoSteps * y
          = 3 ^ w.oddSteps * x + w.affineConst := hyEq
      _ = 2 ^ w.twoSteps * z := hzEq.symm
  exact
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      hmul

/--
minimum tail の n 段目 word。
nonempty を正本側で要求するため長さ `n+1` から開始する。
-/
noncomputable def minimumTailWord
    (O : OddOrbit)
    (n : ℕ) : Word :=
  O.segment O.globalMinimumIndex (n + 1)

/-- minimum tail の n 段目 endpoint。 -/
noncomputable def minimumTailEndpoint
    (O : OddOrbit)
    (n : ℕ) : ℕ :=
  O.value (O.globalMinimumIndex + (n + 1))

/-- minimum tail の各 word は actual normalized run。 -/
theorem runs_minimumTail
    (O : OddOrbit)
    (n : ℕ) :
    Runs (O.minimumTailWord n)
      O.globalMinimumValue
      (O.minimumTailEndpoint n) := by
  classical
  unfold minimumTailWord minimumTailEndpoint
  have hrun := O.runsSegment O.globalMinimumIndex (n + 1)
  simpa [O.value_globalMinimumIndex] using hrun

/-- minimum tail の各 word は valid。 -/
theorem minimumTailWord_valid
    (O : OddOrbit)
    (n : ℕ) :
    (O.minimumTailWord n).Valid :=
  (O.runs_minimumTail n).valid

/-- minimum tail の各 word は nonempty。 -/
theorem minimumTailWord_nonempty
    (O : OddOrbit)
    (n : ℕ) :
    O.minimumTailWord n ≠ [] := by
  classical
  intro hnil
  have hlen := congrArg List.length hnil
  unfold minimumTailWord at hlen
  simp only [O.segment_length, List.length_nil] at hlen
  omega

/-- minimum tail の word family は prefix inclusion で nested。 -/
theorem minimumTailWord_nested
    (O : OddOrbit)
    {m n : ℕ}
    (hmn : m ≤ n) :
    ∃ v : Word,
      O.minimumTailWord m ++ v = O.minimumTailWord n := by
  classical
  let i := O.globalMinimumIndex
  let d := n - m
  refine ⟨O.segment (i + (m + 1)) d, ?_⟩
  unfold minimumTailWord
  change
    O.segment i (m + 1) ++ O.segment (i + (m + 1)) d =
      O.segment i (n + 1)
  calc
    O.segment i (m + 1) ++ O.segment (i + (m + 1)) d
        = O.segment i ((m + 1) + d) :=
          (O.segment_add i (m + 1) d).symm
    _ = O.segment i (n + 1) := by
      congr 1
      dsimp [d]
      omega

/--
minimum tail では全 actual prefix endpoint が anchor `globalMinimumValue` 以上。
-/
theorem minimumTail_allPrefixesSurvive
    (O : OddOrbit)
    (n : ℕ) :
    Word.AllPrefixesSurviveAt
      (O.minimumTailWord n)
      O.globalMinimumValue := by
  classical
  have hfull := O.runs_minimumTail n
  apply
    (Word.allPrefixesSurviveAt_iff_allPrefixStartDefectsNonnegative hfull).2
  intro u v huv
  let i := O.globalMinimumIndex
  have hlenEq := congrArg List.length huv
  have hlen : u.length ≤ n + 1 := by
    unfold minimumTailWord at hlenEq
    simp only [List.length_append, O.segment_length] at hlenEq
    omega
  have huSegment : u = O.segment i u.length := by
    calc
      u = (u ++ v).take u.length := by simp
      _ = (O.minimumTailWord n).take u.length := by rw [huv]
      _ = (O.segment i (n + 1)).take u.length := by
        rfl
      _ = O.segment i u.length :=
        O.segment_take_of_le hlen
  have hrunSegment := O.runsSegment i u.length
  have hrunU :
      Runs u O.globalMinimumValue (O.value (i + u.length)) := by
    rw [huSegment]
    simpa [i, O.value_globalMinimumIndex] using hrunSegment
  have hmin :
      O.globalMinimumValue ≤ O.value (i + u.length) :=
    O.globalMinimumValue_le_value (i + u.length)
  exact
    (hrunU.realizes.start_le_end_iff_startDefect_nonneg).1 hmin

/-- minimum tail の residue modulus は任意の整数閾値を eventually 越える。 -/
theorem minimumTail_modulusEscapes
    (O : OddOrbit) :
    ∀ K : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (Word.residueModulus (O.minimumTailWord n) : ℤ) := by
  classical
  intro K
  cases K with
  | ofNat k =>
      refine ⟨k, ?_⟩
      intro n hn
      have hlen :=
        length_le_twoSteps_of_valid (O.minimumTailWord_valid n)
      have hH :
          n + 1 ≤ (O.minimumTailWord n).twoSteps := by
        have hwlen : (O.minimumTailWord n).length = n + 1 := by
          unfold minimumTailWord
          exact O.segment_length O.globalMinimumIndex (n + 1)
        rw [hwlen] at hlen
        exact hlen
      have hpow :=
        succ_le_two_pow ((O.minimumTailWord n).twoSteps + 1)
      have hkM :
          k < Word.residueModulus (O.minimumTailWord n) := by
        unfold Word.residueModulus
        omega
      have hkMZ :
          (k : ℤ) <
            (Word.residueModulus (O.minimumTailWord n) : ℤ) := by
        exact_mod_cast hkM
      exact hkMZ
  | negSucc k =>
      refine ⟨0, ?_⟩
      intro n hn
      have hpos :
          0 < Word.residueModulus (O.minimumTailWord n) :=
        Word.residueModulus_pos _
      have hposZ :
          (0 : ℤ) < (Word.residueModulus (O.minimumTailWord n) : ℤ) := by
        exact_mod_cast hpos
      omega

/--
## OddOrbit -> NestedSurvivalChain

任意の odd-only orbit の global minimum tail は、その minimum を anchor とする
`NestedSurvivalChain` を canonical に与える。
-/
noncomputable def toNestedSurvivalChain
    (O : OddOrbit) :
    Word.NestedSurvivalChain O.globalMinimumValue := by
  classical
  exact
    { word := O.minimumTailWord
      endpoint := O.minimumTailEndpoint
      valid := O.minimumTailWord_valid
      nonempty := O.minimumTailWord_nonempty
      run := O.runs_minimumTail
      survives := O.minimumTail_allPrefixesSurvive
      nested := fun {_ _} hmn => O.minimumTailWord_nested hmn
      modulusEscapes := O.minimumTail_modulusEscapes }

/--
任意の `OddOrbit` から positive odd anchor と、
その anchor に基づく nested survival chain が存在する。
-/
theorem exists_positive_odd_nestedSurvivalChain
    (O : OddOrbit) :
    ∃ x : ℕ,
      ∃ _C : Word.NestedSurvivalChain x,
        0 < x ∧ Odd x := by
  classical
  exact
    ⟨O.globalMinimumValue,
      O.toNestedSurvivalChain,
      O.globalMinimumValue_pos,
      O.globalMinimumValue_odd⟩

/--
反例用途の薄い corollary。

global minimum が `1` より大きい orbit は、
nontrivial anchor と、その anchor に基づく nested survival chain を与える。
-/
theorem exists_nontrivial_nestedSurvivalChain
    (O : OddOrbit)
    (hmin : 1 < O.globalMinimumValue) :
    ∃ x : ℕ,
      ∃ _C : Word.NestedSurvivalChain x,
        1 < x := by
  classical
  exact
    ⟨O.globalMinimumValue,
      O.toNestedSurvivalChain,
      hmin⟩

/-! ## Unbounded orbit の nontriviality / injectivity -/

/--
odd な自然数は 2 で割り切れない。
normalized step の一意性に使う局所補助定理。
-/
private theorem not_two_dvd_of_odd_local
    {a : ℕ}
    (ha : Odd a) :
    ¬ 2 ∣ a := by
  rcases ha with ⟨k, hk⟩
  intro hdiv
  rcases hdiv with ⟨d, hd⟩
  omega

/--
`e < f` なら、`2^f` は `2^e` にさらに少なくとも一つ `2` を掛けた形になる。
-/
private theorem two_pow_even_factor_of_lt_local
    {e f : ℕ}
    (hlt : e < f) :
    ∃ d : ℕ,
      2 ^ f = 2 ^ e * (2 * 2 ^ d) := by
  obtain ⟨d, hd⟩ :=
    Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
  refine ⟨d, ?_⟩
  rw [hd, pow_add, pow_succ]
  simp [mul_assoc]


/--
`e < f` かつ `2^e * a = 2^f * b` なら、
小さい指数側の odd part `a` は `2` で割れる。
-/
private theorem two_dvd_left_part_of_exponent_lt_local
    {e f a b : ℕ}
    (hlt : e < f)
    (hEq : 2 ^ e * a = 2 ^ f * b) :
    2 ∣ a := by
  obtain ⟨d, hpow⟩ :=
    two_pow_even_factor_of_lt_local hlt
  have hcancel :
      a = (2 * 2 ^ d) * b := by
    apply
      Nat.mul_left_cancel
        (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
    calc
      2 ^ e * a
          = 2 ^ f * b := hEq
      _ = (2 ^ e * (2 * 2 ^ d)) * b := by
            rw [hpow]
      _ = 2 ^ e * ((2 * 2 ^ d) * b) := by
            simp [mul_assoc]
  refine ⟨2 ^ d * b, ?_⟩
  calc
    a = (2 * 2 ^ d) * b := hcancel
    _ = 2 * (2 ^ d * b) := by
          simp [mul_assoc]


/--
2 の冪と odd 数の積が等しければ、
2-adic exponent と odd part はそれぞれ一意。

これは normalized odd-only step の決定性を支える局所補助定理。
-/
private theorem two_pow_mul_odd_unique_local
    {e f a b : ℕ}
    (ha : Odd a)
    (hb : Odd b)
    (hEq : 2 ^ e * a = 2 ^ f * b) :
    e = f ∧ a = b := by
  have hef : e = f := by
    rcases lt_trichotomy e f with hlt | heq | hgt
    · have hdiv : 2 ∣ a :=
        two_dvd_left_part_of_exponent_lt_local hlt hEq
      exact False.elim
        ((not_two_dvd_of_odd_local ha) hdiv)
    · exact heq
    · have hdiv : 2 ∣ b :=
        two_dvd_left_part_of_exponent_lt_local
          hgt
          hEq.symm
      exact False.elim
        ((not_two_dvd_of_odd_local hb) hdiv)
  subst f
  have hab : a = b := by
    exact
      Nat.mul_left_cancel
        (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
        hEq
  exact ⟨rfl, hab⟩

/--
同じ odd value から始まる normalized odd-only step の次の value は一意。
-/
private theorem next_value_eq_of_value_eq
    (O : OddOrbit)
    {m n : ℕ}
    (hEq : O.value m = O.value n) :
    O.value (m + 1) = O.value (n + 1) := by
  have hstep :
      2 ^ O.exponent m * O.value (m + 1) =
        2 ^ O.exponent n * O.value (n + 1) := by
    calc
      2 ^ O.exponent m * O.value (m + 1)
          = 3 * O.value m + 1 := O.step m
      _ = 3 * O.value n + 1 := by rw [hEq]
      _ = 2 ^ O.exponent n * O.value (n + 1) :=
        (O.step n).symm
  exact
    (two_pow_mul_odd_unique_local
      (O.value_odd (m + 1))
      (O.value_odd (n + 1))
      hstep).2

/--
同じ value に到達した二つの時点から先は、
全 future value が一致する。
-/
private theorem value_eq_add_of_value_eq
    (O : OddOrbit)
    {m n : ℕ}
    (hEq : O.value m = O.value n) :
    ∀ k : ℕ,
      O.value (m + k) = O.value (n + k) := by
  intro k
  induction k with
  | zero =>
      simpa using hEq
  | succ k ih =>
      have hnext :=
        next_value_eq_of_value_eq O ih
      simpa [Nat.add_assoc] using hnext

/--
有限 prefix の value を上から抑える elementary bound。
repeat があるとき全軌道を bounded にするためだけに使う。
-/
private def valuePrefixBound
    (O : OddOrbit) : ℕ → ℕ
  | 0 => O.value 0
  | n + 1 =>
      max (valuePrefixBound O n) (O.value (n + 1))

/-- prefix 内の各 value は `valuePrefixBound` 以下。 -/
private theorem value_le_valuePrefixBound
    (O : OddOrbit)
    {k n : ℕ}
    (hkn : k ≤ n) :
    O.value k ≤ valuePrefixBound O n := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp [valuePrefixBound]
  | succ n ih =>
      by_cases hk : k ≤ n
      · exact
          le_trans
            (ih hk)
            (by
              simp [valuePrefixBound])
      · have hkEq : k = n + 1 := by omega
        subst k
        simp [valuePrefixBound]

/--
同じ value が異なる二時点で現れれば、
normalized dynamics の決定性により軌道全体は bounded。

後半は repeat interval を period として何度でも左へ戻せる。
-/
private theorem bounded_of_value_repeat
    (O : OddOrbit)
    {m n : ℕ}
    (hmn : m < n)
    (hEq : O.value m = O.value n) :
    ∃ B : ℕ, ∀ t : ℕ, O.value t ≤ B := by
  let B : ℕ := valuePrefixBound O n
  refine ⟨B, ?_⟩
  intro t
  refine Nat.strong_induction_on t ?_
  intro t ih
  by_cases htn : t ≤ n
  · exact value_le_valuePrefixBound O htn
  · have hnt : n < t := by omega
    let k : ℕ := t - n
    have hnk : n + k = t := by
      dsimp [k]
      omega
    have hmkLt : m + k < t := by
      dsimp [k]
      omega
    have hshift :
        O.value (m + k) = O.value (n + k) :=
      value_eq_add_of_value_eq O hEq k
    have htEq :
        O.value t = O.value (m + k) := by
      calc
        O.value t
            = O.value (n + k) := by rw [hnk]
        _ = O.value (m + k) := hshift.symm
    rw [htEq]
    exact ih (m + k) hmkLt

/--
## Unbounded -> value injective

unbounded odd-only orbit では同じ value を二度通れない。

二度通れば normalized dynamics の決定性により eventual periodic となり、
上の `bounded_of_value_repeat` により bounded になってしまう。
-/
theorem value_injective_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Function.Injective O.value := by
  intro m n hEq
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · obtain ⟨B, hB⟩ :=
      bounded_of_value_repeat O hmn hEq
    obtain ⟨t, ht⟩ := hU B
    exact False.elim ((not_lt_of_ge (hB t)) ht)
  · exact hmn
  · obtain ⟨B, hB⟩ :=
      bounded_of_value_repeat O hnm hEq.symm
    obtain ⟨t, ht⟩ := hU B
    exact False.elim ((not_lt_of_ge (hB t)) ht)

/--
value が1なら、normalized odd-only step の次も1。

`1 -> 1` の normalization exponent は2で一意。
-/
private theorem next_value_eq_one_of_value_eq_one
    (O : OddOrbit)
    {n : ℕ}
    (hn : O.value n = 1) :
    O.value (n + 1) = 1 := by
  have hstep :
      2 ^ O.exponent n * O.value (n + 1) =
        2 ^ 2 * 1 := by
    calc
      2 ^ O.exponent n * O.value (n + 1)
          = 3 * O.value n + 1 := O.step n
      _ = 2 ^ 2 * 1 := by
            rw [hn]
            norm_num
  exact
    (two_pow_mul_odd_unique_local
      (O.value_odd (n + 1))
      (by decide : Odd (1 : ℕ))
      hstep).2

/--
## Unbounded -> nontrivial minimum

unbounded orbit の global minimum は1より大きい。

もし minimum が1なら、その次も1。
しかし unbounded orbit の value は injective なので、
同じ1を連続して取ることはできない。
-/
theorem globalMinimumValue_gt_one_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    1 < O.globalMinimumValue := by
  have hpos : 0 < O.globalMinimumValue :=
    O.globalMinimumValue_pos
  by_contra hnot
  have hminOne :
      O.globalMinimumValue = 1 := by
    omega
  let i : ℕ := O.globalMinimumIndex
  have hi :
      O.value i = 1 := by
    dsimp [i]
    rw [O.value_globalMinimumIndex, hminOne]
  have hnext :
      O.value (i + 1) = 1 :=
    next_value_eq_one_of_value_eq_one O hi
  have hsame :
      O.value i = O.value (i + 1) := by
    calc
      O.value i = 1 := hi
      _ = O.value (i + 1) := hnext.symm
  have hinj :
      Function.Injective O.value :=
    O.value_injective_of_unbounded hU
  have hidx :
      i = i + 1 :=
    hinj hsame
  omega

/--
unbounded orbit の minimum-tail endpoint は injective。
-/
theorem minimumTailEndpoint_injective_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Function.Injective O.minimumTailEndpoint := by
  intro m n hEq
  have hinj :
      Function.Injective O.value :=
    O.value_injective_of_unbounded hU
  unfold minimumTailEndpoint at hEq
  have hidx :=
    hinj hEq
  omega

/--
## Unbounded -> NestedSurvivalChain endpoint injective

`toNestedSurvivalChain` に降ろした後も endpoint は injective。
従って `BarrierEnvelopeEventuallyConstant` の aperiodic 条件を
unbounded orbit から自動供給できる。
-/
theorem toNestedSurvivalChain_endpoint_injective_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Function.Injective
      (O.toNestedSurvivalChain).endpoint := by
  change Function.Injective O.minimumTailEndpoint
  exact O.minimumTailEndpoint_injective_of_unbounded hU

/--
unbounded orbit に対する infinite-survival dichotomy。

minimum anchor は nontrivial であり、
minimum-tail chain の endpoint は injective。
その上で abstract `infiniteSurvivalDichotomy` を actual orbit に適用する。
-/
theorem unbounded_to_infiniteSurvivalDichotomy
    (O : OddOrbit)
    (hU : O.Unbounded) :
    1 < O.globalMinimumValue ∧
      Function.Injective
        (O.toNestedSurvivalChain).endpoint ∧
      (Word.NestedSurvivalChain.ForeverExpanding O.toNestedSurvivalChain ∨
        Word.NestedSurvivalChain.EventuallySingletonSurvival O.toNestedSurvivalChain) := by
  constructor
  · exact O.globalMinimumValue_gt_one_of_unbounded hU
  constructor
  · exact
      O.toNestedSurvivalChain_endpoint_injective_of_unbounded hU
  · exact
      (O.toNestedSurvivalChain).infiniteSurvivalDichotomy

/--
unbounded orbit の contracting branch では、
center barrier の strict record-low 更新は eventually 停止する。
-/
theorem barrierEnvelopeEventuallyConstant_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hex :
      ∃ n : ℕ,
        Word.Contracting
          ((O.toNestedSurvivalChain).word n)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ Word.NestedSurvivalChain.BarrierRecord O.toNestedSurvivalChain n := by
  exact
    (O.toNestedSurvivalChain).barrierEnvelopeEventuallyConstant
      (O.toNestedSurvivalChain_endpoint_injective_of_unbounded hU)
      hex

end OddOrbit


/--
## HasUnboundedOddOrbit -> infinite survival dichotomy

非有界 odd-only orbit が存在するなら、

* `x > 1` である nontrivial minimum anchor
* endpoint が injective な minimum-tail `NestedSurvivalChain`

が存在し、その chain は

  `ForeverExpanding`
    OR
  `EventuallySingletonSurvival`

のどちらかへ必ず落ちる。
-/
theorem hasUnboundedOddOrbit_to_infiniteSurvivalDichotomy :
    HasUnboundedOddOrbit →
      ∃ x : ℕ,
        1 < x ∧
          ∃ C : Word.NestedSurvivalChain x,
            Function.Injective C.endpoint ∧
              (Word.NestedSurvivalChain.ForeverExpanding C ∨
                Word.NestedSurvivalChain.EventuallySingletonSurvival C) := by
  rintro ⟨O, hU⟩
  refine ⟨O.globalMinimumValue, ?_⟩
  constructor
  · exact O.globalMinimumValue_gt_one_of_unbounded hU
  · refine ⟨O.toNestedSurvivalChain, ?_⟩
    constructor
    · exact
        O.toNestedSurvivalChain_endpoint_injective_of_unbounded hU
    · exact
        (O.toNestedSurvivalChain).infiniteSurvivalDichotomy

/--
## HasUnboundedOddOrbit -> strong infinite-survival dichotomy

非有界 odd-only orbit が存在するなら、その global minimum tail から

* nontrivial minimum anchor `x > 1`
* endpoint が injective な `NestedSurvivalChain C`

が得られ、さらに C は exact に次の強い二分岐へ落ちる。

1. 全段が forever expanding。
2. finite-survival start が eventually `x` 一点に孤立し、
   contracting-center の strict record-low 更新も eventually 停止する。

従って contracting 側では

  start freedom -> eventually singleton
  center envelope -> eventually constant

が同時に成立する。
-/
theorem hasUnboundedOddOrbit_to_strongInfiniteSurvivalDichotomy :
    HasUnboundedOddOrbit →
      ∃ x : ℕ,
        1 < x ∧
          ∃ C : Word.NestedSurvivalChain x,
            Function.Injective C.endpoint ∧
              (
                Word.NestedSurvivalChain.ForeverExpanding C
                ∨
                (
                  Word.NestedSurvivalChain.EventuallySingletonSurvival C
                  ∧
                  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                    ¬ Word.NestedSurvivalChain.BarrierRecord C n
                )
              ) := by
  classical
  rintro ⟨O, hU⟩
  let C :
      Word.NestedSurvivalChain O.globalMinimumValue :=
    O.toNestedSurvivalChain
  have hmin :
      1 < O.globalMinimumValue :=
    O.globalMinimumValue_gt_one_of_unbounded hU
  have hInjective :
      Function.Injective C.endpoint := by
    dsimp [C]
    exact
      O.toNestedSurvivalChain_endpoint_injective_of_unbounded hU
  refine ⟨O.globalMinimumValue, hmin, C, hInjective, ?_⟩
  by_cases hE :
      Word.NestedSurvivalChain.ForeverExpanding C
  · exact Or.inl hE
  · right
    /-
    ForeverExpanding でない側では、
    既存の infiniteSurvivalDichotomy の左枝は hE に反するので、
    EventuallySingletonSurvival が残る。
    -/
    have hSingleton :
        Word.NestedSurvivalChain.EventuallySingletonSurvival C := by
      rcases C.infiniteSurvivalDichotomy with hExp | hSingle
      · exact False.elim (hE hExp)
      · exact hSingle
    /-
    ForeverExpanding の否定から、
    expanding でない有限 prefix が少なくとも一つ存在する。
    -/
    have hNotExpanding :
        ∃ m : ℕ, ¬ Word.Expanding (C.word m) := by
      simpa [Word.NestedSurvivalChain.ForeverExpanding] using hE
    obtain ⟨m, hmNotExpanding⟩ := hNotExpanding
    /-
    C.word m は valid nonempty なので determinant は0にならない。
    expanding でなければ contracting。
    -/
    have hmContracting :
        Word.Contracting (C.word m) := by
      rcases
          Word.expanding_or_contracting_of_valid_nonempty
            (C.valid m)
            (C.nonempty m) with hExp | hCon
      · exact False.elim (hmNotExpanding hExp)
      · exact hCon
    /-
    endpoint injectivity と contracting prefix の存在から、
    strict record-low center の更新は eventually 停止する。
    -/
    have hBarrier :
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ¬ Word.NestedSurvivalChain.BarrierRecord C n := by
      exact
        C.barrierEnvelopeEventuallyConstant
          hInjective
          ⟨m, hmContracting⟩
    exact ⟨hSingleton, hBarrier⟩
end Collatz2
