import CollatzLean.Collatz3.Bridge.SurvivorCompletionCocycle

/-!
# Collatz3 Bridge: completion exact lift の直接帰結

このファイルは新しい数学的 data を導入しない。
`SurvivorCompletionArithmetic` / `SurvivorCompletionLift` / `SurvivorCompletionCocycle`
で得た exact theorem から、後続で頻繁に使う帰結を薄い wrapper としてまとめる。

主な内容は

* canonical completion start の通常大小関係での発散下界、
* 異なる幅の completion start が必ず異なること、
* positive defect では roof cut / Record cut が存在しないこと、
* defect `0,1` における自然数 lift coefficient の有限分類。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
十分先では completion start は actual start より少なくとも `2^D_m` 上にある。
-/
theorem start_add_twoPow_le_endpointCompletionStart
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m) :
    O.value 0 + 2 ^ infinitePrefixDepth O.exponent m ≤
      O.endpointCompletionStart SInf (by omega : 0 < m) := by
  rcases O.exists_endpointCompletionNatLift_of_start_succ_le SInf hxm with
    ⟨t, hStart, htPos, _htOdd, _htBound, _hEndpoint⟩
  have htOne : 1 ≤ t := Nat.succ_le_iff.mpr htPos
  have hMul :
      2 ^ infinitePrefixDepth O.exponent m ≤
        2 ^ infinitePrefixDepth O.exponent m * t := by
    have h := Nat.mul_le_mul_left
      (2 ^ infinitePrefixDepth O.exponent m) htOne
    simpa using h
  calc
    O.value 0 + 2 ^ infinitePrefixDepth O.exponent m
        ≤ O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t :=
          Nat.add_le_add_left hMul _
    _ = O.endpointCompletionStart SInf (by omega : 0 < m) := hStart.symm

/-- 十分先では completion start は `2^D_m` 以上。 -/
theorem twoPow_prefixDepth_le_endpointCompletionStart
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m) :
    2 ^ infinitePrefixDepth O.exponent m ≤
      O.endpointCompletionStart SInf (by omega : 0 < m) := by
  have h := O.start_add_twoPow_le_endpointCompletionStart SInf hxm
  omega

/--
十分先では completion start は少なくとも `2^m`。

`m ≤ D_m` と前定理を合わせた、通常の自然数大小での指数的下界。
-/
theorem twoPow_index_le_endpointCompletionStart
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m) :
    2 ^ m ≤ O.endpointCompletionStart SInf (by omega : 0 < m) := by
  have hmD : m ≤ infinitePrefixDepth O.exponent m :=
    O.index_le_infinitePrefixDepth SInf m
  have hPow :
      2 ^ m ≤ 2 ^ infinitePrefixDepth O.exponent m :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hmD
  exact le_trans hPow
    (O.twoPow_prefixDepth_le_endpointCompletionStart SInf hxm)

/--
completion canonical starts は通常の自然数順序でも任意の固定 bound を最終的に越える。

2進的には actual start へ近づく一方、通常の大小では `+∞` へ逃げることの
order-theoretic 版。
-/
theorem endpointCompletionStart_eventually_gt
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (B : ℕ) :
    ∃ M : ℕ,
      ∀ m : ℕ,
        M ≤ m →
        ∀ hm : 0 < m,
          B < O.endpointCompletionStart SInf hm := by
  let M := max (O.value 0 + 1) B
  refine ⟨M, ?_⟩
  intro m hMm hm
  have hxm : O.value 0 + 1 ≤ m :=
    le_trans (Nat.le_max_left _ _) hMm
  have hBm : B ≤ m :=
    le_trans (Nat.le_max_right _ _) hMm
  have hBpow : B < 2 ^ m := by
    have hSelf : B < 2 ^ B := B.lt_two_pow_self
    have hMono : 2 ^ B ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hBm
    exact lt_of_lt_of_le hSelf hMono
  have hC := O.twoPow_index_le_endpointCompletionStart SInf hxm
  have hMain :
      B < O.endpointCompletionStart SInf (by omega : 0 < m) :=
    lt_of_lt_of_le hBpow hC
  simpa using hMain

/--
異なる positive 幅の completion canonical starts は必ず異なる。
-/
theorem endpointCompletionStart_ne_of_lt
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {r s : ℕ}
    (hr : 0 < r)
    (hrs : r < s) :
    O.endpointCompletionStart SInf hr ≠
      O.endpointCompletionStart SInf (lt_trans hr hrs) := by
  have hExact := O.endpointCompletionStart_pair_exact_twoDepth SInf hr hrs
  intro hEq
  apply hExact.2
  rw [hEq]

/-- positive defect の cut は completion roof cut になれない。 -/
theorem endpointCompletion_not_roofCut_of_defect_pos
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (haPos : 0 < a)
    (haLt : a < m)
    (hDefect : 0 < infiniteSurvivorDefect O.exponent a) :
    ¬ Critical.IsRoofCut
        (survivorCriticalCompletionAdmissibleProfile
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1
        a := by
  intro hRoof
  have hZero :=
    (O.endpointCompletion_roofCut_iff_defect_zero
      SInf hm haPos haLt).1 hRoof
  omega

/--
ある index `N` 以降 defect が常に正なら、任意の completion window の
`N` 以降の proper cut は roof に戻らない。
-/
theorem endpointCompletion_no_roofCut_of_eventually_defect_pos
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {N m a : ℕ}
    (hm : 0 < m)
    (haPos : 0 < a)
    (haLt : a < m)
    (hNa : N ≤ a)
    (hEventually :
      ∀ k : ℕ, N ≤ k → 0 < infiniteSurvivorDefect O.exponent k) :
    ¬ Critical.IsRoofCut
        (survivorCriticalCompletionAdmissibleProfile
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1
        a := by
  exact O.endpointCompletion_not_roofCut_of_defect_pos
    SInf hm haPos haLt (hEventually a hNa)

/--
positive defect の cut は primitive best-upper endpoint Record window の
proper Record cut にもなれない。
-/
theorem endpointRecord_not_recordCut_of_defect_pos
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (hWidth : 2 < (O.endpointSurvivorCode SInf m).1.length)
    (P : Critical.IsPrimitiveWidth (O.endpointSurvivorCode SInf m).1.length)
    (Best : Critical.IsBestUpperWidth (O.endpointSurvivorCode SInf m).1.length)
    (hDefect : 0 < infiniteSurvivorDefect O.exponent a) :
    ¬ Ferrers.IsRecordCutAfter
      (survivorRecordWindow
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)
        hWidth P Best).profile.1
      Critical.initialRoofAnchor a := by
  intro hCut
  have hZero := O.endpointRecordCut_defect_zero
    SInf hm hWidth P Best hCut
  omega

/--
`N` 以降 defect が正なら、Record window の proper Record cut は必ず `N` より手前。
-/
theorem endpointRecordCut_lt_of_eventually_defect_pos
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {N m a : ℕ}
    (hm : 0 < m)
    (hWidth : 2 < (O.endpointSurvivorCode SInf m).1.length)
    (P : Critical.IsPrimitiveWidth (O.endpointSurvivorCode SInf m).1.length)
    (Best : Critical.IsBestUpperWidth (O.endpointSurvivorCode SInf m).1.length)
    (hEventually :
      ∀ k : ℕ, N ≤ k → 0 < infiniteSurvivorDefect O.exponent k)
    (hCut : Ferrers.IsRecordCutAfter
      (survivorRecordWindow
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)
        hWidth P Best).profile.1
      Critical.initialRoofAnchor a) :
    a < N := by
  by_contra hNot
  have hNa : N ≤ a := by omega
  have hPos := hEventually a hNa
  have hZero := O.endpointRecordCut_defect_zero
    SInf hm hWidth P Best hCut
  omega

/--
completion の proper roof cut では、その位置の次 exponent は `1` または `2`。
-/
theorem endpointCompletion_roofCut_next_exponent_eq_one_or_two
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (hRoof : Critical.IsRoofCut
      (survivorCriticalCompletionAdmissibleProfile
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)).1
      a) :
    O.exponent a = 1 ∨ O.exponent a = 2 := by
  have hZero := O.endpointCompletion_roofCut_defect_zero SInf hm hRoof
  exact O.exponent_eq_one_or_two_of_defect_zero SInf hZero

/--
primitive best-upper Record window の proper Record cut でも、次 exponent は `1` または `2`。
-/
theorem endpointRecordCut_next_exponent_eq_one_or_two
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (hWidth : 2 < (O.endpointSurvivorCode SInf m).1.length)
    (P : Critical.IsPrimitiveWidth (O.endpointSurvivorCode SInf m).1.length)
    (Best : Critical.IsBestUpperWidth (O.endpointSurvivorCode SInf m).1.length)
    (hCut : Ferrers.IsRecordCutAfter
      (survivorRecordWindow
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)
        hWidth P Best).profile.1
      Critical.initialRoofAnchor a) :
    O.exponent a = 1 ∨ O.exponent a = 2 := by
  have hZero := O.endpointRecordCut_defect_zero SInf hm hWidth P Best hCut
  exact O.exponent_eq_one_or_two_of_defect_zero SInf hZero

/--
terminal residue と canonical modulus 内の範囲だけで lift coefficient は一意。

`3^m` は `2^(E_m+1)` と互いに素なので、

`y_m + 3^m t ≡ 2^E_m (mod 2^(E_m+1))`

を満たす `0 ≤ t < 2^(E_m+1)` は高々一つ。

この一意性自体には infinite survivor 仮定は不要であり、
純粋な合同算術から従う。
-/
theorem endpointCompletionHenselLift_unique
    (O : Collatz3.OddOrbit)
    {m t u : ℕ}
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hT : O.value m + 3 ^ m * t ≡
      2 ^ O.endpointCompletionExtraDepth m
      [MOD 2 ^ (O.endpointCompletionExtraDepth m + 1)])
    (hU : O.value m + 3 ^ m * u ≡
      2 ^ O.endpointCompletionExtraDepth m
      [MOD 2 ^ (O.endpointCompletionExtraDepth m + 1)]) :
    t = u := by
  let M := 2 ^ (O.endpointCompletionExtraDepth m + 1)
  have hSum :
      O.value m + 3 ^ m * t ≡ O.value m + 3 ^ m * u [MOD M] := by
    simpa [M] using hT.trans hU.symm
  have hMul : 3 ^ m * t ≡ 3 ^ m * u [MOD M] := by
    exact Nat.ModEq.add_left_cancel' (O.value m) hSum
  have hGcd : Nat.gcd M (3 ^ m) = 1 := by
    dsimp [M]
    exact
      (Arithmetic.coprime_threePow_twoPow
        m (O.endpointCompletionExtraDepth m + 1)).symm
  have hTU : t ≡ u [MOD M] :=
    hMul.cancel_left_of_coprime hGcd
  exact hTU.eq_of_lt_of_lt (by simpa [M] using ht) (by simpa [M] using hu)

/--
endpoint bridge を満たす二つの bounded lift coefficient は一意。
start equation を使わず、endpoint の Hensel residue だけで比較する wrapper。
-/
theorem endpointCompletionEndpointLift_unique
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hT :
      2 ^ O.endpointCompletionExtraDepth m *
          O.endpointCompletionEnd SInf hm =
        O.value m + 3 ^ m * t)
    (hU :
      2 ^ O.endpointCompletionExtraDepth m *
          O.endpointCompletionEnd SInf hm =
        O.value m + 3 ^ m * u) :
    t = u := by
  have hTR := O.endpointCompletionLift_henselModEq SInf hm hT
  have hUR := O.endpointCompletionLift_henselModEq SInf hm hU
  exact O.endpointCompletionHenselLift_unique ht hu hTR hUR

/--
十分先で defect `0` なら natural lift coefficient は `1` または `3` の二択。
endpoint equation も `2 Y_m = y_m + 3^m t_m` に縮退する。
-/
theorem exists_endpointCompletionNatLift_of_defect_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m)
    (hZero : infiniteSurvivorDefect O.exponent m = 0) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf (by omega : 0 < m) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t ∧
      (t = 1 ∨ t = 3) ∧
      2 * O.endpointCompletionEnd SInf (by omega : 0 < m) =
        O.value m + 3 ^ m * t := by
  rcases O.exists_endpointCompletionNatLift_defect SInf hxm with
    ⟨t, hStart, htPos, htOdd, htBound, hEndpoint⟩
  have htBound' : t < 4 := by
    rw [hZero] at htBound
    norm_num at htBound ⊢
    exact htBound
  have htClass : t = 1 ∨ t = 3 := by
    omega
  have hEndpoint' :
      2 * O.endpointCompletionEnd SInf (by omega : 0 < m) =
        O.value m + 3 ^ m * t := by
    rw [hZero] at hEndpoint
    norm_num at hEndpoint ⊢
    exact hEndpoint
  exact ⟨t, hStart, htClass, hEndpoint'⟩

/--
十分先で defect `1` なら natural lift coefficient は `1,3,5,7` の四択。
-/
theorem exists_endpointCompletionNatLift_of_defect_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m)
    (hOne : infiniteSurvivorDefect O.exponent m = 1) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf (by omega : 0 < m) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t ∧
      (t = 1 ∨ t = 3 ∨ t = 5 ∨ t = 7) ∧
      4 * O.endpointCompletionEnd SInf (by omega : 0 < m) =
        O.value m + 3 ^ m * t := by
  rcases O.exists_endpointCompletionNatLift_defect SInf hxm with
    ⟨t, hStart, htPos, htOdd, htBound, hEndpoint⟩
  have htBound' : t < 8 := by
    rw [hOne] at htBound
    norm_num at htBound ⊢
    exact htBound
  have htClass : t = 1 ∨ t = 3 ∨ t = 5 ∨ t = 7 := by
    omega
  have hEndpoint' :
      4 * O.endpointCompletionEnd SInf (by omega : 0 < m) =
        O.value m + 3 ^ m * t := by
    rw [hOne] at hEndpoint
    norm_num at hEndpoint ⊢
    exact hEndpoint
  exact ⟨t, hStart, htClass, hEndpoint'⟩


/--
十分先の proper roof cut は、その cut 自身の width completion で
二状態 lift `t∈{1,3}` を持つ。
-/
theorem exists_smallNatLift_of_endpointCompletion_roofCut
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (hxa : O.value 0 + 1 ≤ a)
    (hRoof : Critical.IsRoofCut
      (survivorCriticalCompletionAdmissibleProfile
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)).1
      a) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf (by omega : 0 < a) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent a * t ∧
      (t = 1 ∨ t = 3) ∧
      2 * O.endpointCompletionEnd SInf (by omega : 0 < a) =
        O.value a + 3 ^ a * t := by
  have hZero := O.endpointCompletion_roofCut_defect_zero SInf hm hRoof
  exact O.exists_endpointCompletionNatLift_of_defect_zero SInf hxa hZero

/--
十分先の proper Record cut も、その cut 自身の width completion で
二状態 lift `t∈{1,3}` を持つ。
-/
theorem exists_smallNatLift_of_endpointRecordCut
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (hxa : O.value 0 + 1 ≤ a)
    (hWidth : 2 < (O.endpointSurvivorCode SInf m).1.length)
    (P : Critical.IsPrimitiveWidth (O.endpointSurvivorCode SInf m).1.length)
    (Best : Critical.IsBestUpperWidth (O.endpointSurvivorCode SInf m).1.length)
    (hCut : Ferrers.IsRecordCutAfter
      (survivorRecordWindow
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)
        hWidth P Best).profile.1
      Critical.initialRoofAnchor a) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf (by omega : 0 < a) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent a * t ∧
      (t = 1 ∨ t = 3) ∧
      2 * O.endpointCompletionEnd SInf (by omega : 0 < a) =
        O.value a + 3 ^ a * t := by
  have hZero := O.endpointRecordCut_defect_zero SInf hm hWidth P Best hCut
  exact O.exists_endpointCompletionNatLift_of_defect_zero SInf hxa hZero

end OddOrbit
end Collatz3
