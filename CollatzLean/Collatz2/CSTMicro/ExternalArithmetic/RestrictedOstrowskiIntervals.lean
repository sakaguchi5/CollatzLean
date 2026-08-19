import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ProfileIntervalCostBlocks

/-!
# Stage 8A: canonical Ostrowski partition の interval restriction

prefix `[0,b)` の canonical Ostrowski scale list を、途中の cut `a ≤ b` から読み直す。

重要なのは、cut が block の途中に落ちたとき、その block の残りだけを一つの
left boundary fragment として取り、その後は既存 `actualCriticalPhaseDefectFold` を
そのまま使うことである。従って restricted fold には boundary fragment は高々一つしか
現れず、その後は全部 canonical whole phase blocks である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
`left` から始まる scale partition を cut `a` から読む restricted defect fold。

* cut が current block より右なら current block を捨てて再帰する。
* cut が current block 内なら `[a,mid)` を唯一の fragment とし、tail は ordinary fold。
* cut が current left と一致すれば ordinary fold そのもの。
-/
def restrictedCriticalPhaseDefectFold :
    ℕ → ℕ → List ℕ → ℤ → ℤ
  | _, _, [], _ => 0
  | a, left, r :: rs, y =>
      let mid := left + criticalPowerP r
      if a ≤ left then
        actualCriticalPhaseDefectFold left (r :: rs) y
      else if mid ≤ a then
        restrictedCriticalPhaseDefectFold a mid rs y
      else
        (3 : ℤ) ^ actualCriticalBlockScaleMass rs *
            criticalIntervalDefectZ a mid y +
          (2 : ℤ) ^ (beattyIndex mid - beattyIndex a) *
            actualCriticalPhaseDefectFold mid rs y

/-- cut が current left 以下なら restricted fold は ordinary fold そのもの。 -/
private theorem restrictedCriticalPhaseDefectFold_cons_of_cut_le_left
    {a left r : ℕ}
    {rs : List ℕ}
    {y : ℤ}
    (hCutLeft : a ≤ left) :
    restrictedCriticalPhaseDefectFold a left (r :: rs) y =
      actualCriticalPhaseDefectFold left (r :: rs) y := by
  simp only [
    restrictedCriticalPhaseDefectFold,
    if_pos hCutLeft
  ]


/-- current block が cut より完全に左なら、その block を捨てて再帰する。 -/
private theorem restrictedCriticalPhaseDefectFold_cons_of_mid_le_cut
    {a left r : ℕ}
    {rs : List ℕ}
    {y : ℤ}
    (hLeftCut : left < a)
    (hMidCut : left + criticalPowerP r ≤ a) :
    restrictedCriticalPhaseDefectFold a left (r :: rs) y =
      restrictedCriticalPhaseDefectFold
        a (left + criticalPowerP r) rs y := by
  have hNotLeft : ¬ a ≤ left := by
    omega
  simp only [
    restrictedCriticalPhaseDefectFold,
    if_neg hNotLeft,
    if_pos hMidCut
  ]


/-- cut が current block の内部なら、その block を唯一の restricted fragment にする。 -/
private theorem restrictedCriticalPhaseDefectFold_cons_of_cut_inside
    {a left r : ℕ}
    {rs : List ℕ}
    {y : ℤ}
    (hLeftCut : left < a)
    (hCutMid : a < left + criticalPowerP r) :
    restrictedCriticalPhaseDefectFold a left (r :: rs) y =
      (3 : ℤ) ^ actualCriticalBlockScaleMass rs *
          criticalIntervalDefectZ
            a (left + criticalPowerP r) y +
        (2 : ℤ) ^
            (beattyIndex (left + criticalPowerP r) - beattyIndex a) *
          actualCriticalPhaseDefectFold
            (left + criticalPowerP r) rs y := by
  have hNotLeft : ¬ a ≤ left := by
    omega
  have hNotMid : ¬ left + criticalPowerP r ≤ a := by
    omega
  simp only [
    restrictedCriticalPhaseDefectFold,
    if_neg hNotLeft,
    if_neg hNotMid
  ]


/--
interval `[a, mid + mass(rs))` を `mid` で切ると、

* 左 fragment の defect
* `mid` から始まる ordinary tail fold

へ exact に分解される。
-/
private theorem criticalIntervalDefectZ_eq_fragment_add_phaseTail
    (a mid : ℕ)
    (rs : List ℕ)
    (y : ℤ)
    (hAMid : a ≤ mid) :
    criticalIntervalDefectZ
        a (mid + actualCriticalBlockScaleMass rs) y =
      (3 : ℤ) ^ actualCriticalBlockScaleMass rs *
          criticalIntervalDefectZ a mid y +
        (2 : ℤ) ^ (beattyIndex mid - beattyIndex a) *
          actualCriticalPhaseDefectFold mid rs y := by
  have hMidFinish :
      mid ≤ mid + actualCriticalBlockScaleMass rs := by
    omega
  have hConcat :=
    criticalIntervalDefectZ_concat
      (a := a)
      (c := mid)
      (b := mid + actualCriticalBlockScaleMass rs)
      hAMid
      hMidFinish
      y
  have hTail :=
    criticalIntervalDefectZ_eq_phaseDefectFold mid rs y
  have hExp :
      mid + actualCriticalBlockScaleMass rs - mid =
        actualCriticalBlockScaleMass rs := by
    omega
  rw [hConcat, hExp, hTail]


/--
restricted fold は exact に interval `[a, left + mass(scales))` の defect。

scale list 上の induction では、

* cut = current left なら whole-block fold
* current block が cut より左なら induction hypothesis
* cut が current block 内なら fragment + ordinary tail

の3場合だけが残る。
-/
theorem criticalIntervalDefectZ_eq_restrictedCriticalPhaseDefectFold
    (left a : ℕ)
    (scales : List ℕ)
    (y : ℤ)
    (hLeft : left ≤ a)
    (hFinish : a ≤ left + actualCriticalBlockScaleMass scales) :
    criticalIntervalDefectZ
        a (left + actualCriticalBlockScaleMass scales) y =
      restrictedCriticalPhaseDefectFold a left scales y := by
  induction scales generalizing left with
  | nil =>
      have hEq : a = left := by
        simp only [
          actualCriticalBlockScaleMass_nil,
          Nat.add_zero
        ] at hFinish
        omega
      subst a
      simp [restrictedCriticalPhaseDefectFold]
  | cons r rs ih =>
      let mid := left + criticalPowerP r
      have hMass :
          left + actualCriticalBlockScaleMass (r :: rs) =
            mid + actualCriticalBlockScaleMass rs := by
        dsimp [mid]
        simp [actualCriticalBlockScaleMass, Nat.add_assoc]
      rw [hMass] at hFinish ⊢
      by_cases hCutLeft : a ≤ left
      · -- hLeft と合わせると cut = current left。
        have hEq : a = left := by
          omega
        subst a
        have hRestricted :
            restrictedCriticalPhaseDefectFold
                left left (r :: rs) y =
              actualCriticalPhaseDefectFold left (r :: rs) y := by
          exact
            restrictedCriticalPhaseDefectFold_cons_of_cut_le_left
              (a := left)
              (left := left)
              (r := r)
              (rs := rs)
              (y := y)
              le_rfl
        rw [hRestricted]
        have hWhole :=
          criticalIntervalDefectZ_eq_phaseDefectFold
            left (r :: rs) y
        rw [hMass] at hWhole
        exact hWhole
      · have hLeftLt : left < a := by
          omega
        by_cases hMidCut : mid ≤ a
        · -- current block は cut より完全に左。
          have hRestricted :
              restrictedCriticalPhaseDefectFold
                  a left (r :: rs) y =
                restrictedCriticalPhaseDefectFold
                  a mid rs y := by
            simpa [mid] using
              restrictedCriticalPhaseDefectFold_cons_of_mid_le_cut
                (a := a)
                (left := left)
                (r := r)
                (rs := rs)
                (y := y)
                hLeftLt
                (by simpa [mid] using hMidCut)
          rw [hRestricted]
          exact ih mid hMidCut hFinish
        · -- cut は current block の内部。
          have hCutMid : a < mid := by
            omega
          have hRestricted :
              restrictedCriticalPhaseDefectFold
                  a left (r :: rs) y =
                (3 : ℤ) ^ actualCriticalBlockScaleMass rs *
                    criticalIntervalDefectZ a mid y +
                  (2 : ℤ) ^
                      (beattyIndex mid - beattyIndex a) *
                    actualCriticalPhaseDefectFold mid rs y := by
            simpa [mid] using
              restrictedCriticalPhaseDefectFold_cons_of_cut_inside
                (a := a)
                (left := left)
                (r := r)
                (rs := rs)
                (y := y)
                hLeftLt
                (by simpa [mid] using hCutMid)
          rw [hRestricted]
          exact
            criticalIntervalDefectZ_eq_fragment_add_phaseTail
              a mid rs y (Nat.le_of_lt hCutMid)


/-- arbitrary prefix `b` の canonical partition を cut `a` から読む値。 -/
def actualCriticalRestrictedPhaseDefectFold
    (a b : ℕ)
    (y : ℤ) : ℤ :=
  restrictedCriticalPhaseDefectFold
    a 0 (actualCriticalOstrowskiBlockScales b) y

/--
`a ≤ b` なら canonical prefix partition の restriction は exact に `F[a,b](y)`。
-/
theorem criticalIntervalDefectZ_eq_actualCriticalRestrictedPhaseDefectFold
    {a b : ℕ}
    (hab : a ≤ b)
    (y : ℤ) :
    criticalIntervalDefectZ a b y =
      actualCriticalRestrictedPhaseDefectFold a b y := by
  unfold actualCriticalRestrictedPhaseDefectFold
  have h :=
    criticalIntervalDefectZ_eq_restrictedCriticalPhaseDefectFold
      0 a (actualCriticalOstrowskiBlockScales b) y
      (by omega)
      (by
        rw [actualCriticalOstrowskiBlockScales_mass_eq]
        simpa using hab)
  rw [actualCriticalOstrowskiBlockScales_mass_eq] at h
  simpa using h

end ExternalArithmetic
end CSTMicro
end Collatz2
