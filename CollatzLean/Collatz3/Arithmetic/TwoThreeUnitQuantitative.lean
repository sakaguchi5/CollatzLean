import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit

/-!
# Collatz3 Arithmetic: `{2,3}`-unit exponent bound の定量版

既存の `NondegenerateTwoThreeUnitExponentBound` は

`∀ N, ∃ K, ... k < K`

という存在形だけを保持する。

このファイルでは bound を関数 `F : ℕ → ℕ` として外へ出した薄い interface
`NondegenerateTwoThreeUnitExponentBoundBy F` を追加する。

新しい数論仮定は導入しない。既存の存在形から classical choice で
ある `F` を選べることも証明する。
-/

namespace Collatz3
namespace Arithmetic

/--
`N` 項以下の nondegenerate `{2,3}`-unit equation に `-3^k` が現れるなら、
`k < F N` である、という定量版 interface。
-/
def NondegenerateTwoThreeUnitExponentBoundBy
    (F : ℕ → ℕ) : Prop :=
  ∀ N : ℕ,
    ∀ {ι : Type} [DecidableEq ι],
      ∀ (term : ι → SignedTwoThreeUnit)
        (s : Finset ι)
        (k : ℕ),
        s.card ≤ N →
        NondegenerateSumOne
          (fun i => (term i).value) s →
        (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
        k < F N

/-- 定量版から既存の存在版を忘却する。 -/
theorem NondegenerateTwoThreeUnitExponentBoundBy.to_exists
    {F : ℕ → ℕ}
    (h : NondegenerateTwoThreeUnitExponentBoundBy F) :
    NondegenerateTwoThreeUnitExponentBound := by
  intro N
  refine ⟨F N, ?_⟩
  intro ι inst term s k hCard hNondegenerate hThree
  exact h N term s k hCard hNondegenerate hThree

/--
既存の存在版 bound から classical choice で一つの bound function を選ぶ。

この関数に growth rate の情報は一切入っていない。
-/
noncomputable def chosenTwoThreeUnitExponentBound
    (h : NondegenerateTwoThreeUnitExponentBound)
    (N : ℕ) : ℕ :=
  Classical.choose (h N)

/-- chosen bound function は定量版 interface を満たす。 -/
theorem chosenTwoThreeUnitExponentBound_spec
    (h : NondegenerateTwoThreeUnitExponentBound) :
    NondegenerateTwoThreeUnitExponentBoundBy
      (chosenTwoThreeUnitExponentBound h) := by
  intro N
  exact Classical.choose_spec (h N)

/--
存在版 exponent bound があれば、それを実現する何らかの bound function `F` が存在する。

これは growth rate を主張する定理ではなく、量化順序を関数形に直しただけである。
-/
theorem exists_twoThreeUnitExponentBoundFunction
    (h : NondegenerateTwoThreeUnitExponentBound) :
    ∃ F : ℕ → ℕ,
      NondegenerateTwoThreeUnitExponentBoundBy F := by
  exact ⟨chosenTwoThreeUnitExponentBound h,
    chosenTwoThreeUnitExponentBound_spec h⟩

end Arithmetic
end Collatz3
