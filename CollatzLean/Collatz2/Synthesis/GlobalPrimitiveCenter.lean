import CollatzLean.Collatz2.Synthesis.PrimitiveCenter

/-!
# Collatz2 Synthesis: global primitive-center rise on the negative tail

`EventuallyNegative`、future-minimum 値の eventual largeness、
`omegaAdjacent > 0` の cofinality、primitive center factorization を一本につなぐ。

新しい branch data は導入しない。
negative divergence tail では元の adjacent block のまま
primitive separation `kappa >= 1` が cofinally 強制される。
-/

namespace Collatz2
namespace Synthesis

namespace AdjacentTransferChain

/--
eventually-negative branch では primitive center separation `kappa >= 1` が cofinal。

必要な四条件

* block `n` が negative
* block `n+1` も negative
* start future minimum が `> 1`
* `omegaAdjacent n > 0`

はすべて sufficiently late な `omega > 0` event 上で同時に満たされる。
-/
theorem primitiveKappa_one_le_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => (1 : ℤ) ≤ primitiveKappa C n) := by
  have hOmega : Cofinal (fun n => 0 < omegaAdjacent C n) :=
    omegaAdjacent_pos_cofinal_of_eventuallyNegative C hE
  rcases hE with ⟨Nneg, hNeg⟩
  obtain ⟨Nval, hVal⟩ := C.minima.values_eventually_large 1
  intro M
  let L := max M (max Nneg Nval)
  obtain ⟨n, hnL, hOmegaN⟩ := hOmega L
  have hML : M ≤ L := le_max_left _ _
  have hTailL : max Nneg Nval ≤ L := le_max_right _ _
  have hNegL : Nneg ≤ L :=
    le_trans (le_max_left _ _) hTailL
  have hValL : Nval ≤ L :=
    le_trans (le_max_right _ _) hTailL
  have hnM : M ≤ n := le_trans hML hnL
  have hnNeg : Nneg ≤ n := le_trans hNegL hnL
  have hnVal : Nval ≤ n := le_trans hValL hnL
  have hN : C.NegativeAt n := hNeg n hnNeg
  have hNs : C.NegativeAt (n + 1) := hNeg (n + 1) (by omega)
  have hstart : 1 < C.startValue n := by
    have h := hVal n hnVal
    simpa [AdjacentTransferChain.startValue,
      AdjacentTransferChain.startIndex] using h
  exact ⟨n, hnM,
    one_le_primitiveKappa_of_omegaAdjacent_pos
      C hN hNs hstart hOmegaN⟩

/-- eventually-negative branch では `primitiveKappa > 0` も cofinal。 -/
theorem primitiveKappa_pos_cofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hE : C.EventuallyNegative) :
    Cofinal (fun n => 0 < primitiveKappa C n) := by
  have hK := primitiveKappa_one_le_cofinal_of_eventuallyNegative C hE
  intro M
  obtain ⟨n, hnM, hnK⟩ := hK M
  exact ⟨n, hnM, lt_of_lt_of_le (by omega) hnK⟩

end AdjacentTransferChain
end Synthesis
end Collatz2
