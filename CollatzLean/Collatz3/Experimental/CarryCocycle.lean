import CollatzLean.Collatz3.Experimental.UnitCarryRoof

/-!
# Collatz3 experimental: roof carry の cocycle と有限 block 合成

全面書き換え前の第二段数学実験。

`HasUnitCarry β` の carry を局所的な 0/1 値として見るだけでなく、
複数 block を連結したときの「加法欠損の保存量」として調べる。

ここでは現行 `Critical` / `Ferrers` / `RecordFerrers` は使わない。
保存する data は block 列から有限計算される `carryListFrom` だけであり、
その長さ・総和・最大値・合成則は theorem として導く。
-/

namespace Collatz3
namespace Experimental

/--
start `a` から block length 列 `rs` を順に連結したとき、
各境界で発生する roof carry を左から並べた有限列。
-/
def carryListFrom
    (β : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _a, [] => []
  | a, r :: rs =>
      roofCarry β a r :: carryListFrom β (a + r) rs

/-- carry 列の長さは block 数そのもの。 -/
@[simp] theorem carryListFrom_length
    {β : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      (carryListFrom β a rs).length = rs.length
  | _a, [] => by
      rfl
  | a, r :: rs => by
      simp [carryListFrom, carryListFrom_length (β := β) (a + r) rs]

/--
block 列を `xs ++ ys` に分けても carry 列は lossless に連結できる。
後半の start は前半 block width の総和だけ進めればよい。
-/
theorem carryListFrom_append
    {β : ℕ → ℕ} :
    ∀ (a : ℕ) (xs ys : List ℕ),
      carryListFrom β a (xs ++ ys) =
        carryListFrom β a xs ++
          carryListFrom β (a + xs.sum) ys
  | _a, [], ys => by
      simp [carryListFrom]
  | a, r :: rs, ys => by
      simp [carryListFrom,
        carryListFrom_append (β := β) (a + r) rs ys,
        Nat.add_assoc]

namespace HasUnitCarry

/-- `HasUnitCarry` だけから屋根原点 `β(0)=0` が強制される。 -/
theorem zero_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    β 0 = 0 := by
  have h : β 0 + β 0 ≤ β 0 := by
    simpa using (U 0 0).1
  omega

/-- 左に幅 0 を足した carry は 0。 -/
theorem carry_zero_left
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ) :
    roofCarry β 0 a = 0 := by
  have hZero := U.zero_eq
  simp [roofCarry, hZero]

/-- 右に幅 0 を足した carry は 0。 -/
theorem carry_zero_right
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ) :
    roofCarry β a 0 = 0 := by
  have hZero := U.zero_eq
  simp [roofCarry, hZero]

/--
carry の cocycle identity。

`c(a,b) + c(a+b,d) = c(b,d) + c(a,b+d)`。

三つの区間を `(a+b)+d` と `a+(b+d)` のどちらで結合しても
同じ屋根高さへ到達することの exact な保存則。
-/
theorem carry_cocycle
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b d : ℕ) :
    roofCarry β a b + roofCarry β (a + b) d =
      roofCarry β b d + roofCarry β a (b + d) := by
  have hAB := U.add_eq a b
  have hAB_D := U.add_eq (a + b) d
  have hBD := U.add_eq b d
  have hA_BD := U.add_eq a (b + d)
  have hAssoc : (a + b) + d = a + (b + d) := by
    omega
  rw [hAssoc] at hAB_D
  omega

/-- carry 列の各成分は高々 1。 -/
theorem carryListFrom_mem_le_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ {a : ℕ} {rs : List ℕ} {c : ℕ},
      c ∈ carryListFrom β a rs →
      c ≤ 1
  | _a, [], _c, hMem => by
      simp [carryListFrom] at hMem
  | a, r :: rs, c, hMem => by
      simp only [carryListFrom, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · subst c
        exact U.carry_le_one a r
      · exact U.carryListFrom_mem_le_one hTail

/-- carry 総和は block 数以下。 -/
theorem carryListFrom_sum_le_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ (a : ℕ) (rs : List ℕ),
      (carryListFrom β a rs).sum ≤ rs.length
  | _a, [] => by
      simp [carryListFrom]
  | a, r :: rs => by
      have hHead := U.carry_le_one a r
      have hTail := U.carryListFrom_sum_le_length (a + r) rs
      simp only [carryListFrom, List.sum_cons, List.length_cons]
      omega

/--
有限 block 合成の exact roof equation。

`β(a + Σ rᵢ) = β(a) + Σ β(rᵢ) + Σ carryᵢ`。

したがって carry 総和は、block 分割に対する roof の加法欠損そのものになる。
-/
theorem roof_add_sum_eq_blockRoofs_add_carries
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ (a : ℕ) (rs : List ℕ),
      β (a + rs.sum) =
        β a + (rs.map β).sum + (carryListFrom β a rs).sum
  | a, [] => by
      simp [carryListFrom]
  | a, r :: rs => by
      have hHead := U.add_eq a r
      have hTail :=
        U.roof_add_sum_eq_blockRoofs_add_carries (a + r) rs
      simp only [
        List.sum_cons,
        List.map_cons,
        carryListFrom
      ]
      have hIndex :
          a + (r + rs.sum) = (a + r) + rs.sum := by
        omega
      rw [hIndex]
      omega

/--
carry 総和が取り得る最大値 `block数` に達したなら、
全境界 carry は強制的に `1`。
-/
theorem carryListFrom_eq_replicate_one_of_sum_eq_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ (a : ℕ) (rs : List ℕ),
      (carryListFrom β a rs).sum = rs.length →
      carryListFrom β a rs = List.replicate rs.length 1
  | _a, [], _hMax => by
      simp [carryListFrom]
  | a, r :: rs, hMax => by
      have hHeadLe := U.carry_le_one a r
      have hTailLe := U.carryListFrom_sum_le_length (a + r) rs
      have hHeadOne : roofCarry β a r = 1 := by
        simp only [carryListFrom, List.sum_cons, List.length_cons] at hMax
        omega
      have hTailMax :
          (carryListFrom β (a + r) rs).sum = rs.length := by
        simp only [carryListFrom, List.sum_cons, List.length_cons] at hMax
        omega
      have hTailOnes :=
        U.carryListFrom_eq_replicate_one_of_sum_eq_length
          (a + r) rs hTailMax
      simp [carryListFrom, hHeadOne, hTailOnes]
      rfl

/--
最後の境界 carry が `0` で、全 carry 総和が `pre.length` なら、
境界列全体は exact に `1, ..., 1, 0`。

これは RecordFerrers をまだ使わない純粋な有限 0/1-carry 定理。
-/
theorem carryListFrom_append_singleton_eq_ones_then_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (pre : List ℕ)
    (r : ℕ)
    (hLastZero : roofCarry β (a + pre.sum) r = 0)
    (hTotal :
      (carryListFrom β a (pre ++ [r])).sum = pre.length) :
    carryListFrom β a (pre ++ [r]) =
      List.replicate pre.length 1 ++ [0] := by
  have hAppend :=
    carryListFrom_append (β := β) a pre [r]
  rw [hAppend] at hTotal
  have hPreMax :
      (carryListFrom β a pre).sum = pre.length := by
    simpa [carryListFrom, hLastZero] using hTotal
  have hPreOnes :=
    U.carryListFrom_eq_replicate_one_of_sum_eq_length
      a pre hPreMax
  rw [carryListFrom_append (β := β) a pre [r]]
  simp [carryListFrom, hLastZero, hPreOnes]

end HasUnitCarry
end Experimental
end Collatz3
