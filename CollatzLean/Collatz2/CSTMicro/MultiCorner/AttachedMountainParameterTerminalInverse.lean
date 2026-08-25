import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedMountainParameterLeftIdentity

/-!
# MultiCorner attached branch: mountain parameter の terminal inverse condition

terminal mountain parameter の peak/drop equations

  peak = a * 3^W - 1
  2^l * z = peak

から

  2^l | (a * 3^W - 1)

を exact に取り出す。したがって `a` は `3^W` の inverse class modulo `2^l` を表す。
ここで `l = evenRunLength` であり、mountain word `[1^(W-1), d]` なら `l=d-1`。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
right terminal drop が与える 2-adic inverse condition。

congruence を divisor form で保持することで、後段の Hensel/Farey bridge から直接使える。
-/
theorem mountainParameter_terminal_inverse
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {w : Collatz2.Word}
    {x z a peak : ℕ}
    (T : Collatz2.Word.MountainRun w x z)
    (hWidth :
      T.shape.oddRunLength = A.straightHenselWidth)
    (hPeak :
      peak = a * 3 ^ T.shape.oddRunLength - 1)
    (hDesc :
      2 ^ T.shape.evenRunLength * z = peak) :
    2 ^ T.shape.evenRunLength ∣
      a * 3 ^ A.straightHenselWidth - 1 := by
  rw [← hWidth]
  refine ⟨z, ?_⟩
  calc
    a * 3 ^ T.shape.oddRunLength - 1
        = peak := hPeak.symm
    _ = 2 ^ T.shape.evenRunLength * z := hDesc.symm

end AttachedTwoCornerPacket
end MultiCorner
end CSTMicro
end Collatz2
