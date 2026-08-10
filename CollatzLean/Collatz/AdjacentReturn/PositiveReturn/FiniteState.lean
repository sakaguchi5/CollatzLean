import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.Valuation

/-!
# bounded-depth finite-state refinement

positive-return chain の gap-depth が有界な枝では、浅い start 上に
任意に長い first crossing が現れる。early first-high 情報を有限型へ圧縮する。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn

/-- depth bound `M` の下で保持する有限 shallow signature。 -/
structure ShallowSignatureValue (M : ℕ) where
  startDepth : Fin (M + 1)
  firstHighOffset : Fin (M + 1)
  firstHighExponent : Fin (M + 1)
deriving DecidableEq, Fintype

namespace CanonicalChain

/-- shallow start の early first-high 情報を有限 signature へ落とす。 -/
noncomputable def shallowSignature
    {O : OddOrbit} (C : CanonicalChain O)
    (M n : ℕ)
    (hshallow : C.core.startDepth n ≤ M) :
    ShallowSignatureValue M := by
  let H := C.core.startFirstHigh n
  have hshallow' :
      (C.core.valuationData n).startDepth ≤ M := by
    simpa [CanonicalContractingChain.startDepth] using hshallow
  have hcontrol :=
    C.core.shallow_firstHigh_control
      (M := M) (n := n) hshallow'
  exact {
    startDepth := ⟨C.core.startDepth n, by omega⟩
    firstHighOffset := ⟨H.offset, by
      have hH : H.offset < M := by
        simpa [H] using hcontrol.1
      omega⟩
    firstHighExponent :=
      ⟨O.exponent ((C.state n).startIndex + H.offset), by
        have h := hcontrol.2.1
        have hle :
            O.exponent ((C.state n).startIndex + H.offset) ≤ M := by
          simpa [H, state] using h
        omega⟩
  }

/-- bounded gap-depth 枝では浅い start 上に任意に長い positive first crossing がある。 -/
theorem arbitrarily_long_shallow_firstCrossing
    {O : OddOrbit} (C : CanonicalChain O)
    {M : ℕ}
    (hB : C.core.GapDepthBounded M) :
    ∀ L : ℕ,
      ∃ n : ℕ,
        C.core.startDepth n ≤ M ∧
        L < (C.firstCrossing n).length := by
  intro L
  obtain ⟨n, hshallow, hlong⟩ :=
    C.core.arbitrarily_long_shallow_firstCrossing_of_gapDepth_bounded
      hB L
  exact ⟨n, hshallow, hlong (C.firstCrossing n)⟩

/-- bounded枝の任意に長い項には有限 shallow signature を付けられる。 -/
theorem arbitrarily_long_shallow_signature
    {O : OddOrbit} (C : CanonicalChain O)
    {M : ℕ}
    (hB : C.core.GapDepthBounded M) :
    ∀ L : ℕ,
      ∃ n : ℕ,
      ∃ hshallow : C.core.startDepth n ≤ M,
        L < (C.firstCrossing n).length ∧
          C.shallowSignature M n hshallow ∈
            (Finset.univ : Finset (ShallowSignatureValue M)) := by
  intro L
  obtain ⟨n, hshallow, hlong⟩ :=
    C.arbitrarily_long_shallow_firstCrossing hB L
  exact ⟨n, hshallow, hlong, Finset.mem_univ _⟩

/--
有限 pigeonhole 後に残すべき fixed-signature obstruction。
この structure 自体は proof target として使い、一般 pigeonhole の供給とは分離する。
-/
structure RecurrentShallowSignatureData
    {O : OddOrbit} (C : CanonicalChain O) (M : ℕ) where
  signature : ShallowSignatureValue M
  unbounded :
    ∀ L : ℕ,
      ∃ n : ℕ,
      ∃ hshallow : C.core.startDepth n ≤ M,
        C.shallowSignature M n hshallow = signature ∧
          L < (C.firstCrossing n).length

/-- positive-return chain にも既存 gap-depth bounded/unbounded 二分岐がそのまま載る。 -/
theorem gapDepth_bounded_or_unbounded
    {O : OddOrbit} (C : CanonicalChain O) :
    (∃ M : ℕ, C.core.GapDepthBounded M) ∨
      C.core.GapDepthUnbounded :=
  C.core.gapDepth_bounded_or_unbounded

end CanonicalChain
end PositiveReturn
end AdjacentReturn
end Collatz
