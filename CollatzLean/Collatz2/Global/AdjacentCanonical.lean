import CollatzLean.Collatz2.Global.AdjacentTransferChain
import CollatzLean.Collatz2.Canonical.ReplayExtremality

/-!
# Collatz2 Global: adjacent chain の canonical corollary

`AdjacentTransferChain` 自体は future minima / actual Runs / affine transfer だけを保持する
lossless global source object とし、canonical / replay 層へ依存させない。

negative adjacent positive return から canonical (`q=0`) positive return を導く
corollary だけをこの bridge module に分離する。
-/

namespace Collatz2
namespace AdjacentTransferChain

/--
negative determinant の adjacent positive return は replay extremality により
canonical (`q=0`) positive return を強制する。
-/
theorem canonical_positive_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Word.canonicalStart (C.word n) <
      Word.canonicalEnd (C.word n) := by
  have hC : Word.Contracting (C.word n) :=
    (C.negativeAt_iff_contracting n).1 hN
  exact
    (C.runs n).canonical_positive_of_contracting_positive
      (C.word_nonempty n)
      hC
      (C.startValue_lt_endValue n)

end AdjacentTransferChain
end Collatz2
