import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RankDropArithmetic

/-!
# Collatz3 Experimental2: canonical boundary collision の算術障害

F8 では internal diagonal corner の同時発生を

* canonical width の累積 endpoint
* reverse rank-drop の累積 endpoint

の衝突として exact に記述した。
F9 では `gcd(m, criticalDepth β m)` が各 rank drop を割ることを得た。

本ファイルではこの二つを接続する。

主結果は次の二点。

1. canonical boundary collision が level `t` で起きるなら、
   `gcd(m, criticalDepth β m)` は `t` を割る。
2. internal collision が一つでもあれば basis equality は破れ、
   F5 の下界と F6 の parity から actual Young 面積は basis 面積より少なくとも `2` 大きい。

従って collision は単なる yes/no 条件ではなく、最初の定量的 obstruction を与える。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/--
正整数列の累積 endpoint `t` があり、各 block が整数 `g` の倍数なら、
endpoint `t` も `g` の倍数。
`BoundaryAtWidths` の再帰定義に直接沿う薄い補題。
-/
theorem boundaryAtWidths_int_dvd
    (g : ℕ) :
    ∀ {xs : List ℕ} {t : ℕ},
      BoundaryAtWidths xs t →
      (∀ x ∈ xs, (g : ℤ) ∣ (x : ℤ)) →
      (g : ℤ) ∣ (t : ℤ)
  | [], _t, hB, _hAll => by
      simp [BoundaryAtWidths] at hB
  | r :: rs, t, hB, hAll => by
      simp only [BoundaryAtWidths] at hB
      rcases hB with hEq | ⟨hrt, hTail⟩
      · subst t
        exact hAll r (by simp)
      · have hr : (g : ℤ) ∣ (r : ℤ) :=
          hAll r (by simp)
        have hRestAll :
            ∀ x ∈ rs, (g : ℤ) ∣ (x : ℤ) := by
          intro x hx
          exact hAll x (by simp [hx])
        have hTailDvd :
            (g : ℤ) ∣ ((t - r : ℕ) : ℤ) :=
          boundaryAtWidths_int_dvd g hTail hRestAll
        rcases hr with ⟨a, ha⟩
        rcases hTailDvd with ⟨b, hb⟩
        refine ⟨b + a, ?_⟩
        have hsum : t - r + r = t :=
          Nat.sub_add_cancel (Nat.le_of_lt hrt)
        have hsumZ :
            (((t - r : ℕ) : ℤ) + (r : ℤ)) = (t : ℤ) := by
          exact_mod_cast hsum
        rw [← hsumZ, hb, ha]
        ring

/--
`BoundaryAtWidths xs t` なら、`xs` の非空 prefix で和が `t` になるものが存在する。
F8 の再帰 boundary を通常の prefix-sum equation へ戻すための witness theorem。
-/
theorem boundaryAtWidths_exists_prefixSum :
    ∀ {xs : List ℕ} {t : ℕ},
      BoundaryAtWidths xs t →
      ∃ pre suf : List ℕ,
        xs = pre ++ suf ∧
          pre ≠ [] ∧
            pre.sum = t
  | [], _t, hB => by
      simp [BoundaryAtWidths] at hB
  | r :: rs, t, hB => by
      simp only [BoundaryAtWidths] at hB
      rcases hB with hEq | ⟨hrt, hTail⟩
      · subst t
        exact ⟨[r], rs, by simp, by simp, by simp⟩
      · rcases boundaryAtWidths_exists_prefixSum hTail with
          ⟨pre, suf, hSplit, hNonempty, hSum⟩
        refine ⟨r :: pre, suf, ?_, by simp, ?_⟩
        · rw [hSplit]
          rfl
        · simp only [List.sum_cons]
          omega

/--
map 後の boundary から、元 list の非空 prefix と mapped sum equation を回収する。
reverse canonical lengths 上の rank-drop boundary を扱うために使う。
-/
theorem boundaryAtWidths_map_exists_prefixSum
    (f : ℕ → ℕ) :
    ∀ {xs : List ℕ} {t : ℕ},
      BoundaryAtWidths (xs.map f) t →
      ∃ pre suf : List ℕ,
        xs = pre ++ suf ∧
          pre ≠ [] ∧
            (pre.map f).sum = t
  | [], _t, hB => by
      simp [BoundaryAtWidths] at hB
  | r :: rs, t, hB => by
      simp only [List.map_cons, BoundaryAtWidths] at hB
      rcases hB with hEq | ⟨hrt, hTail⟩
      · subst t
        exact ⟨[r], rs, by simp, by simp, by simp⟩
      · rcases boundaryAtWidths_map_exists_prefixSum f hTail with
          ⟨pre, suf, hSplit, hNonempty, hSum⟩
        refine ⟨r :: pre, suf, ?_, by simp, ?_⟩
        · rw [hSplit]
          rfl
        · simp only [List.map_cons, List.sum_cons]
          omega

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted
open GenericRecordFerrers

/--
完成 RecordFerrers の一つの canonical block の自然数 rank drop は
`gcd(m, criticalDepth β m)` の倍数。
-/
theorem canonicalRankDropNat_rankDropGcd_dvd
    {β : ℕ → ℕ}
    {m r : ℕ}
    (R : RecordFerrers β m)
    (hr : r ∈ canonicalRecordLengths β m R.height) :
    (rankDropGcd β m : ℤ) ∣ (rankDropNat β m r : ℤ) := by
  have hpos : 0 < rankDropInt β m r :=
    positiveRankDrop_of_mem R.positiveRankDrops hr
  exact rankDropGcd_dvd_rankDropNat_cast_of_pos hpos

/-- rank-drop height boundary は必ず terminal gcd modulus の倍数 level にある。 -/
theorem rankDropHeightBoundaryAt_rankDropGcd_dvd
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hB : R.rankDropHeightBoundaryAt t) :
    (rankDropGcd β m : ℤ) ∣ (t : ℤ) := by
  unfold rankDropHeightBoundaryAt at hB
  apply boundaryAtWidths_int_dvd (rankDropGcd β m) hB
  intro x hx
  have hxMap :
      x ∈ (canonicalRecordLengths β m R.height).map (rankDropNat β m) := by
    simpa using hx
  rcases List.mem_map.mp hxMap with ⟨r, hr, hEq⟩
  subst x
  exact R.canonicalRankDropNat_rankDropGcd_dvd hr

/-- canonical boundary collision の level は terminal gcd modulus の倍数。 -/
theorem hasCanonicalBoundaryCollision_rankDropGcd_dvd
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (rankDropGcd β m : ℤ) ∣ (t : ℤ) := by
  exact R.rankDropHeightBoundaryAt_rankDropGcd_dvd hC.2

/-- 同じ divisibility を自然数上で読む版。 -/
theorem hasCanonicalBoundaryCollision_rankDropGcd_dvd_nat
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hC : R.HasCanonicalBoundaryCollision t) :
    rankDropGcd β m ∣ t := by
  exact_mod_cast R.hasCanonicalBoundaryCollision_rankDropGcd_dvd hC

/--
正の level が gcd modulus より小さければ canonical collision は起こらない。
従って internal diagonal の候補は `g,2g,3g,...` に限られる。
-/
theorem noCanonicalBoundaryCollision_of_lt_rankDropGcd
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (hlt : t < rankDropGcd β m) :
    ¬ R.HasCanonicalBoundaryCollision t := by
  intro hC
  have hDvd := R.hasCanonicalBoundaryCollision_rankDropGcd_dvd_nat hC
  have hLe : rankDropGcd β m ≤ t := Nat.le_of_dvd ht hDvd
  omega

/--
Durfee depth が gcd modulus 以下なら、全 internal diagonal level で collision は不可能。
terminal tightness は別条件なので、この theorem は internal part だけを述べる。
-/
theorem noInternalCanonicalBoundaryCollision_of_depth_le_rankDropGcd
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (hDepth :
      frobeniusDepth R.plateauWidthDropCode ≤ rankDropGcd β m)
    {t : ℕ}
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode) :
    ¬ R.HasCanonicalBoundaryCollision t := by
  apply R.noCanonicalBoundaryCollision_of_lt_rankDropGcd ht
  omega

/--
canonical width boundary から、canonical length 列の非空 prefix と exact sum `t` を回収する。
-/
theorem canonicalWidthBoundaryAt_exists_prefixSum
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hB : R.canonicalWidthBoundaryAt t) :
    ∃ pre suf : List ℕ,
      canonicalRecordLengths β m R.height = pre ++ suf ∧
        pre ≠ [] ∧
          pre.sum = t := by
  unfold canonicalWidthBoundaryAt at hB
  exact boundaryAtWidths_exists_prefixSum hB

/--
rank-drop height boundary から、reverse canonical length 列の非空 prefix を回収する。
この prefix は元の canonical length 列では suffix に対応する。
その rank-drop sum は exact に boundary level `t`。
-/
theorem rankDropHeightBoundaryAt_exists_reversePrefixSum
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hB : R.rankDropHeightBoundaryAt t) :
    ∃ pre suf : List ℕ,
      (canonicalRecordLengths β m R.height).reverse = pre ++ suf ∧
        pre ≠ [] ∧
          rankDropNatSum β m pre = t := by
  unfold rankDropHeightBoundaryAt at hB
  have hB' :
      BoundaryAtWidths
        ((canonicalRecordLengths β m R.height).reverse.map (rankDropNat β m)) t := by
    simpa using hB
  rcases boundaryAtWidths_map_exists_prefixSum (rankDropNat β m) hB' with
    ⟨pre, suf, hSplit, hNonempty, hSum⟩
  refine ⟨pre, suf, hSplit, hNonempty, ?_⟩
  rw [rankDropNatSum_eq_map_sum]
  exact hSum

/--
rank-drop height boundary を reverse canonical-length prefix の整数 rank-drop sum として読む。
自然数化で失われないことは canonical block の strict positivity から従う。
-/
theorem rankDropHeightBoundaryAt_exists_rankDropIntSum
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hB : R.rankDropHeightBoundaryAt t) :
    ∃ pre suf : List ℕ,
      (canonicalRecordLengths β m R.height).reverse = pre ++ suf ∧
        pre ≠ [] ∧
          (t : ℤ) = rankDropIntSum β m pre := by
  rcases R.rankDropHeightBoundaryAt_exists_reversePrefixSum hB with
    ⟨pre, suf, hSplit, hNonempty, hNatSum⟩
  have hPos : PositiveRankDrops β m pre := by
    apply positiveRankDrops_of_forall_mem β m pre
    intro r hr
    have hrRev : r ∈ (canonicalRecordLengths β m R.height).reverse := by
      rw [hSplit]
      simp [hr]
    have hrOrig : r ∈ canonicalRecordLengths β m R.height := by
      simpa using hrRev
    exact positiveRankDrop_of_mem R.positiveRankDrops hrOrig
  have hCast :=
    rankDropNatSum_cast_eq_rankDropIntSum_of_positive β m pre hPos
  have hNatSumZ :
      (rankDropNatSum β m pre : ℤ) = (t : ℤ) := by
    exact_mod_cast hNatSum
  have hIntSum : (t : ℤ) = rankDropIntSum β m pre := by
    rw [← hCast, hNatSumZ]
  exact ⟨pre, suf, hSplit, hNonempty, hIntSum⟩

/--
rank-drop height boundary の suffix 側を `criticalDepth` の線形式まで完全展開する。
`pre` は reverse canonical lengths の prefix、すなわち元順序では terminal 側 suffix。
-/
theorem rankDropHeightBoundaryAt_exists_criticalDepthEquation
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hB : R.rankDropHeightBoundaryAt t) :
    ∃ pre suf : List ℕ,
      (canonicalRecordLengths β m R.height).reverse = pre ++ suf ∧
        pre ≠ [] ∧
          (t : ℤ) =
            (m : ℤ) * (pre.map (fun r => (criticalDepth β r : ℤ))).sum -
              (criticalDepth β m : ℤ) * (pre.sum : ℤ) := by
  rcases R.rankDropHeightBoundaryAt_exists_rankDropIntSum hB with
    ⟨pre, suf, hSplit, hNonempty, hIntSum⟩
  refine ⟨pre, suf, hSplit, hNonempty, ?_⟩
  rw [hIntSum]
  exact rankDropIntSum_eq_criticalDepthFormula β m pre

/--
canonical boundary collision を prefix-width = suffix-rank-drop の明示的 Diophantine equation として展開する。
左 `pre` は canonical lengths の prefix、右 `revTail` は reverse canonical lengths の prefix。
従って `revTail` は元順序では terminal 側 suffix を表す。
-/
theorem hasCanonicalBoundaryCollision_exists_criticalDepthEquation
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (hC : R.HasCanonicalBoundaryCollision t) :
    ∃ pre preRest revTail revRest : List ℕ,
      canonicalRecordLengths β m R.height = pre ++ preRest ∧
        pre ≠ [] ∧
        (canonicalRecordLengths β m R.height).reverse = revTail ++ revRest ∧
        revTail ≠ [] ∧
        pre.sum = t ∧
        (pre.sum : ℤ) =
          (m : ℤ) * (revTail.map (fun r => (criticalDepth β r : ℤ))).sum -
            (criticalDepth β m : ℤ) * (revTail.sum : ℤ) := by
  rcases R.canonicalWidthBoundaryAt_exists_prefixSum hC.1 with
    ⟨pre, preRest, hPreSplit, hPreNonempty, hPreSum⟩
  rcases R.rankDropHeightBoundaryAt_exists_criticalDepthEquation hC.2 with
    ⟨revTail, revRest, hRevSplit, hRevNonempty, hEq⟩
  refine ⟨pre, preRest, revTail, revRest,
    hPreSplit, hPreNonempty, hRevSplit, hRevNonempty, hPreSum, ?_⟩
  have hPreSumZ : (pre.sum : ℤ) = (t : ℤ) := by
    exact_mod_cast hPreSum
  rw [hPreSumZ]
  exact hEq

/--
`start ... start+n-1` の internal diagonal に collision があれば、
その区間の canonical plateau basis condition は成立しない。
-/
theorem canonicalPlateauBasisConditionFrom_false_of_internalCollision
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    ∀ (start n t : ℕ),
      start < t →
      t < start + n →
      R.HasCanonicalBoundaryCollision t →
      ¬ R.CanonicalPlateauBasisConditionFrom start n
  | _start, 0, _t, hStart, hEnd, _hC => by
      omega
  | start, 1, t, hStart, hEnd, _hC => by
      omega
  | start, n + 2, t, hStart, hEnd, hC => by
      intro hBasis
      simp only [CanonicalPlateauBasisConditionFrom] at hBasis
      by_cases hEq : t = start + 1
      · subst t
        exact hBasis.1 hC
      · have hNext : start + 1 < t := by omega
        exact
          R.canonicalPlateauBasisConditionFrom_false_of_internalCollision
            (start + 1) (n + 1) t hNext (by omega) hC hBasis.2

/-- whole shape の internal collision は canonical basis condition を破る。 -/
theorem canonicalPlateauBasisCondition_false_of_internalCollision
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    ¬ R.CanonicalPlateauBasisCondition := by
  unfold CanonicalPlateauBasisCondition
  exact
    R.canonicalPlateauBasisConditionFrom_false_of_internalCollision
      0 (frobeniusDepth R.plateauWidthDropCode) t ht (by simpa using htD) hC

/-- internal collision があれば actual Young 面積は basis weight と等しくない。 -/
theorem youngCellCount_ne_basisWeightZ_of_internalCollision
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (R.youngCellCount : ℤ) ≠ basisWeightZ R.successiveRanks := by
  intro hEq
  have hBasis : R.CanonicalPlateauBasisCondition :=
    (R.youngCellCount_eq_basisWeightZ_iff_canonicalPlateauBasisCondition).1 hEq
  exact (R.canonicalPlateauBasisCondition_false_of_internalCollision ht htD hC) hBasis

/--
最初の quantitative obstruction。
internal canonical boundary collision が一つでもあれば、
actual Young 面積は basis 最小面積より少なくとも `2` 大きい。

F5 の下界、F6 の偶奇性、F8 の equality characterization だけから従う。
-/
theorem two_le_youngCellCount_sub_basisWeightZ_of_internalCollision
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (2 : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  have hLe := R.basisWeightZ_le_youngCellCount
  have hNe := R.youngCellCount_ne_basisWeightZ_of_internalCollision ht htD hC
  rcases R.youngCellCount_sub_basisWeightZ_eq_two_mul with ⟨k, hk⟩
  omega

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
