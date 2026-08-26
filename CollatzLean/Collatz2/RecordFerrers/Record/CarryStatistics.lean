import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential
import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordFerrersFactorization

/-!
# Record–Ferrers RF-A+5: critical carry statistics

critical carry を単なる局所 gluing bit ではなく、block length list 全体に沿う
0/1-valued statistics として扱う。

主結果:

* critical height の arbitrary block-list telescope
* minimal depth sum と zero-carry count の exact identity
* full record skeleton では zero carry は exact に 1 個
* zero-carry count は block length permutation に対して不変
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- `start` から block length list に沿って現れる critical carry の列。 -/
def carryValuesFrom (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | r :: rs =>
      criticalCarry start r :: carryValuesFrom (start + r) rs

/-- carry 列の総和。各 carry は 0/1 なので、これは carry-one の個数でもある。 -/
def carrySumFrom (start : ℕ) (rs : List ℕ) : ℕ :=
  (carryValuesFrom start rs).sum

/-- block 境界のうち critical carry が 0 になる箇所の個数。 -/
def zeroCarryCountFrom (start : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs =>
      (if criticalCarry start r = 0 then 1 else 0) +
        zeroCarryCountFrom (start + r) rs

@[simp] theorem carryValuesFrom_nil (start : ℕ) :
    carryValuesFrom start [] = [] := rfl

@[simp] theorem carryValuesFrom_cons
    (start r : ℕ)
    (rs : List ℕ) :
    carryValuesFrom start (r :: rs) =
      criticalCarry start r :: carryValuesFrom (start + r) rs := rfl

@[simp] theorem carryValuesFrom_length
    (start : ℕ)
    (rs : List ℕ) :
    (carryValuesFrom start rs).length = rs.length := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
      simp [carryValuesFrom, ih]

/-- carry list の各要素は 1 以下。 -/
theorem carryValuesFrom_mem_le_one
    {start : ℕ}
    {rs : List ℕ}
    {c : ℕ}
    (hc : c ∈ carryValuesFrom start rs) :
    c ≤ 1 := by
  induction rs generalizing start with
  | nil =>
      simp [carryValuesFrom] at hc
  | cons r rs ih =>
      simp only [carryValuesFrom, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact criticalCarry_le_one start r
      · exact ih hc

/-- carry-one count と zero-carry count の和は block 数そのもの。 -/
theorem carrySum_add_zeroCarryCount_eq_length
    (start : ℕ)
    (rs : List ℕ) :
    carrySumFrom start rs + zeroCarryCountFrom start rs = rs.length := by
  induction rs generalizing start with
  | nil =>
      simp [carrySumFrom, carryValuesFrom, zeroCarryCountFrom]
  | cons r rs ih =>
      have hCases := criticalCarry_eq_zero_or_one start r
      have hIH :
          (carryValuesFrom (start + r) rs).sum +
              zeroCarryCountFrom (start + r) rs =
            rs.length := by
        simpa [carrySumFrom] using ih (start + r)
      unfold carrySumFrom
      simp only [
        carryValuesFrom,
        List.sum_cons,
        zeroCarryCountFrom,
        List.length_cons
      ]
      rcases hCases with hZero | hOne
      · rw [hZero]
        simp
        omega
      · rw [hOne]
        simp
        omega

@[simp] theorem carrySumFrom_cons
    (start r : ℕ)
    (rs : List ℕ) :
    carrySumFrom start (r :: rs) =
      criticalCarry start r +
        carrySumFrom (start + r) rs := by
  simp [carrySumFrom, carryValuesFrom]

/--
arbitrary block length list に対する critical height の exact telescope。
carry の寄与は `carrySumFrom` に全て集約される。
-/
theorem criticalHeight_telescope
    (start : ℕ)
    (rs : List ℕ) :
    criticalHeight (start + rs.sum) =
      criticalHeight start +
        (rs.map criticalHeight).sum +
        carrySumFrom start rs := by
  induction rs generalizing start with
  | nil =>
      simp [carrySumFrom, carryValuesFrom]
  | cons r rs ih =>
      have hCrit :=
        criticalHeight_add_eq start r
      have hTail :=
        ih (start + r)
      simp only [
        List.sum_cons,
        List.map_cons,
        carrySumFrom_cons
      ]
      rw [← Nat.add_assoc start r rs.sum]
      rw [hTail, hCrit]
      omega

/--
minimal local depth を全 block に足したときの excess は、
critical carry 0 の個数と exact に一致する。
-/
theorem criticalHeight_add_localMinimalDepthSum_eq_add_zeroCarryCount
    (start : ℕ)
    (rs : List ℕ) :
    criticalHeight start + localMinimalDepthSum rs =
      criticalHeight (start + rs.sum) + zeroCarryCountFrom start rs := by
  induction rs generalizing start with
  | nil =>
      simp [localMinimalDepthSum, zeroCarryCountFrom]
  | cons r rs ih =>
      have hTail :
          criticalHeight (start + r) +
              (rs.map minimalDepth).sum =
            criticalHeight (start + r + rs.sum) +
              zeroCarryCountFrom (start + r) rs := by
        simpa [localMinimalDepthSum] using ih (start + r)
      have hCrit := criticalHeight_add_eq start r
      have hCases := criticalCarry_eq_zero_or_one start r
      simp only [localMinimalDepthSum, List.map_cons, List.sum_cons,
        minimalDepth, zeroCarryCountFrom]
      rw [← Nat.add_assoc start r rs.sum]
      rcases hCases with hZero | hOne
      · rw [hZero] at hCrit
        simp [hZero]
        omega
      · rw [hOne] at hCrit
        simp [hOne]
        omega

/-- full carry condition では zero carry は最後の 1 個だけ。 -/
theorem zeroCarryCount_eq_one_of_full
    (start : ℕ)
    (rs : List ℕ)
    (hCarry : carryConditionFrom start rs) :
    zeroCarryCountFrom start rs = 1 := by
  induction rs generalizing start with
  | nil =>
      simp [carryConditionFrom] at hCarry
  | cons r rs ih =>
      cases rs with
      | nil =>
          have hZero : criticalCarry start r = 0 := by
            simpa [carryConditionFrom] using hCarry
          simp [zeroCarryCountFrom, hZero]
      | cons s ss =>
          have hPair :=
            (carryConditionFrom_cons_cons start r s ss).1 hCarry
          have hHead : criticalCarry start r = 1 := hPair.1
          have hTail :
              carryConditionFrom (start + r) (s :: ss) := hPair.2
          have hIH :=
            ih (start + r) hTail
          rw [zeroCarryCountFrom, hHead]
          simpa using hIH


/-- full carry skeleton では carry-one の個数は block 数から 1 を引いたもの。 -/
theorem carrySum_eq_length_sub_one_of_full
    (start : ℕ)
    (rs : List ℕ)
    (hCarry : carryConditionFrom start rs) :
    carrySumFrom start rs = rs.length - 1 := by
  have hCount := carrySum_add_zeroCarryCount_eq_length start rs
  have hZero := zeroCarryCount_eq_one_of_full start rs hCarry
  rw [hZero] at hCount
  omega

/--
zero-carry count は block length list の permutation に依存しない。
局所 carry の並び自体は変わっても、critical-height telescope の両端が固定する。
-/
theorem zeroCarryCountFrom_perm
    {start : ℕ}
    {rs ss : List ℕ}
    (hPerm : rs.Perm ss) :
    zeroCarryCountFrom start rs = zeroCarryCountFrom start ss := by
  have hSum : rs.sum = ss.sum :=
    List.Perm.sum_eq hPerm
  have hMinimalSum : localMinimalDepthSum rs = localMinimalDepthSum ss := by
    unfold localMinimalDepthSum
    exact List.Perm.sum_eq (List.Perm.map minimalDepth hPerm)
  have hR :=
    criticalHeight_add_localMinimalDepthSum_eq_add_zeroCarryCount start rs
  have hS :=
    criticalHeight_add_localMinimalDepthSum_eq_add_zeroCarryCount start ss
  rw [hSum, hMinimalSum] at hR
  omega

/-- full carry compatible skeleton の local minimal depth telescope を zero-carry language で再取得。 -/
theorem criticalHeight_add_localMinimalDepthSum_of_full
    (start : ℕ)
    (rs : List ℕ)
    (hCarry : carryConditionFrom start rs) :
    criticalHeight start + localMinimalDepthSum rs =
      criticalHeight (start + rs.sum) + 1 := by
  rw [criticalHeight_add_localMinimalDepthSum_eq_add_zeroCarryCount,
      zeroCarryCount_eq_one_of_full start rs hCarry]

end Skeleton

end RecordFerrers
end Collatz2
