import CollatzLean.Collatz3.CSTMicro.ParityExpansion
import CollatzLean.Collatz3.Core.EndpointEquation

/-!
# Collatz3 CSTMicro: parity 展開と odd-only affine data の一致

valid exponent word を standard parity word へ展開しても、

* odd coefficient `3^p`
* two coefficient `2^H`
* affine translation `B`

は変わらない。

したがって standard parity affine equation と既存 `Word.EndpointEquation` は exact に同値になる。
-/

namespace Collatz3
namespace CSTMicro

/-- valid exponent word の parity affine numerator は `Word.affineConst` と一致。 -/
theorem affineConst_expandWord_eq_wordAffineConst
    {w : Word}
    (hValid : Word.Valid w) :
    affineConst (expandWord w) = Word.affineConst w := by
  induction w with
  | nil => simp
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Word.Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      rw [expandWord_cons]
      rw [affineConst_append]
      rw [affineConst_parityBlock]
      rw [oddCount_expandWord]
      rw [length_parityBlock_of_pos he]
      rw [ih hTail]
      simp [Word.affineConst_cons]

/-- parity 展開後の standard affine equation は odd-only endpoint equation と同じ。 -/
theorem affineRealizes_expandWord_iff_wordEndpointEquation
    {w : Word}
    (hValid : Word.Valid w)
    (x y : ℕ) :
    AffineRealizes (expandWord w) x y ↔
      Word.EndpointEquation w x y := by
  rw [Word.endpointEquation_iff]
  unfold AffineRealizes
  rw [length_expandWord_of_valid hValid]
  rw [oddCount_expandWord]
  rw [affineConst_expandWord_eq_wordAffineConst hValid]

/-- exact parity trace からも同じ odd-only whole endpoint equation が得られる。 -/
theorem TraceRealizes.wordEndpointEquation_of_expandWord
    {w : Word}
    (hValid : Word.Valid w)
    {x y : ℕ}
    (h : TraceRealizes (expandWord w) x y) :
    Word.EndpointEquation w x y :=
  (affineRealizes_expandWord_iff_wordEndpointEquation hValid x y).1 h.affine

end CSTMicro
end Collatz3
