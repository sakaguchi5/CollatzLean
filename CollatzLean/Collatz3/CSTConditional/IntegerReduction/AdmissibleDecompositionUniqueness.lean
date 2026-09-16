import CollatzLean.Collatz3.CSTConditional.IntegerReduction.RightRecordCharacterization

/-!
# Collatz3 CSTConditional IntegerReduction: 許容 block 分解の一意性

同じ positive exponent stream `e` に二つの許容 block length 列 `r,s` が与えられたとする。

前ファイルで boundary は

`未来全体に対する strict right-record`

として exponent stream だけから内在的に特徴付けられた。
従って二つの分解は同じ boundary 集合を持つ。

さらに boundary 列は strict monotone なので、同じ boundary 集合を 0 から順に列挙する方法は一意。
その結果、boundary index 列も block length 列も exact に一致する。

線形成長条件、actual orbit、Global CST は使わない。
-/

namespace Collatz3
namespace IntegerReduction

/--
二つの許容分解が同じ exponent stream を分解するなら、
対応する boundary index は各段階で一致する。
-/
theorem admissibleDecomposition_boundaryIndex_eq
    {e r s : ℕ → ℕ}
    (hr : IsAdmissibleDecomposition e r)
    (hs : IsAdmissibleDecomposition e s) :
    ∀ n : ℕ,
      boundaryIndex r n = boundaryIndex s n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let A : ℕ := boundaryIndex r (n + 1)
      let B : ℕ := boundaryIndex s (n + 1)
      have hARecord : IsRightScaleRecord e A := by
        dsimp [A]
        exact hr.boundary_isRightScaleRecord (n + 1)
      have hBRecord : IsRightScaleRecord e B := by
        dsimp [B]
        exact hs.boundary_isRightScaleRecord (n + 1)
      obtain ⟨k, hk⟩ :=
        (hs.isRightScaleRecord_iff_exists_boundary A).1 hARecord
      obtain ⟨l, hl⟩ :=
        (hr.isRightScaleRecord_iff_exists_boundary B).1 hBRecord
      have hrMono := hr.boundaryIndex_strictMono
      have hsMono := hs.boundaryIndex_strictMono
      have hPrevA : boundaryIndex r n < A := by
        dsimp [A]
        exact hrMono (Nat.lt_succ_self n)
      have hPrevB : boundaryIndex s n < B := by
        dsimp [B]
        exact hsMono (Nat.lt_succ_self n)
      have hnk : n < k := by
        by_contra hNot
        have hkLe : k ≤ n := Nat.le_of_not_gt hNot
        have hLe : boundaryIndex s k ≤ boundaryIndex s n :=
          hsMono.monotone hkLe
        rw [← hk, ← ih] at hLe
        omega
      have hnl : n < l := by
        by_contra hNot
        have hlLe : l ≤ n := Nat.le_of_not_gt hNot
        have hLe : boundaryIndex r l ≤ boundaryIndex r n :=
          hrMono.monotone hlLe
        rw [← hl, ih] at hLe
        omega
      have hBA : B ≤ A := by
        calc
          B = boundaryIndex s (n + 1) := rfl
          _ ≤ boundaryIndex s k := hsMono.monotone (by omega)
          _ = A := hk.symm
      have hAB : A ≤ B := by
        calc
          A = boundaryIndex r (n + 1) := rfl
          _ ≤ boundaryIndex r l := hrMono.monotone (by omega)
          _ = B := hl.symm
      exact le_antisymm hAB hBA

/-- 同じ exponent stream の許容 block length 列は一意。 -/
theorem admissibleDecomposition_unique
    {e r s : ℕ → ℕ}
    (hr : IsAdmissibleDecomposition e r)
    (hs : IsAdmissibleDecomposition e s) :
    r = s := by
  funext n
  have hBoundaryN := admissibleDecomposition_boundaryIndex_eq hr hs n
  have hBoundarySucc := admissibleDecomposition_boundaryIndex_eq hr hs (n + 1)
  rw [boundaryIndex_succ, boundaryIndex_succ, hBoundaryN] at hBoundarySucc
  omega

/-- 存在する許容 block 分解はちょうど一つ。 -/
theorem existsUnique_admissibleDecomposition_lengths
    (e : ℕ → ℕ) :
    (∃ r : ℕ → ℕ, IsAdmissibleDecomposition e r) →
      ∃! r : ℕ → ℕ, IsAdmissibleDecomposition e r := by
  rintro ⟨r, hr⟩
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact admissibleDecomposition_unique hs hr

end IntegerReduction
end Collatz3
