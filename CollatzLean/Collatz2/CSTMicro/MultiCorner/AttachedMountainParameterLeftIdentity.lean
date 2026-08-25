import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedActualTerminalMountain
import CollatzLean.Collatz2.Mountain.MountainRunStandardParameterOdd
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileDefectBridge

/-!
# MultiCorner attached branch: mountain parameter の left-history identity

attached terminal mountain の開始 state `x` が、actual left prefix の affine equation

  3^s R + A_s = 2^p x

を満たし、mountain parameter が

  x = a * 2^W - 1

を満たすとき、両者を exact に glue して

  3^s R + A_s + 2^p = 2^(p+W) * a

を得る。

ここで

  s = straightHenselStart
  W = straightHenselWidth
  A_s = profileAffineNumerator s P.h
  p = profileCheckpoint P.h s

である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
left actual affine state と terminal mountain parameter の exact gluing。

`R` には actual application で `leastRepresentative M.word` を入れる。
-/
theorem mountainParameter_left_identity
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {w : Collatz2.Word}
    {x z R a : ℕ}
    (T : Collatz2.Word.MountainRun w x z)
    (hWidth :
      T.shape.oddRunLength = A.straightHenselWidth)
    (haPos : 0 < a)
    (hStart :
      x = a * 2 ^ T.shape.oddRunLength - 1)
    (hPrefix :
      3 ^ A.straightHenselStart * R +
          profileAffineNumerator A.straightHenselStart P.h =
        2 ^ profileCheckpoint P.h A.straightHenselStart * x) :
    3 ^ A.straightHenselStart * R +
          profileAffineNumerator A.straightHenselStart P.h +
          2 ^ profileCheckpoint P.h A.straightHenselStart =
      2 ^
          (profileCheckpoint P.h A.straightHenselStart +
            A.straightHenselWidth) * a := by
  have hStartW :
      x = a * 2 ^ A.straightHenselWidth - 1 := by
    rw [← hWidth]
    exact hStart
  have hProdPos :
      0 < a * 2 ^ A.straightHenselWidth :=
    Nat.mul_pos haPos (Nat.pow_pos (by omega))
  have hxAdd :
      x + 1 = a * 2 ^ A.straightHenselWidth := by
    rw [hStartW]
    omega
  calc
    3 ^ A.straightHenselStart * R +
          profileAffineNumerator A.straightHenselStart P.h +
          2 ^ profileCheckpoint P.h A.straightHenselStart
        =
      2 ^ profileCheckpoint P.h A.straightHenselStart * x +
        2 ^ profileCheckpoint P.h A.straightHenselStart := by
          rw [hPrefix]
    _ =
      2 ^ profileCheckpoint P.h A.straightHenselStart * (x + 1) := by
        ring
    _ =
      2 ^ profileCheckpoint P.h A.straightHenselStart *
        (a * 2 ^ A.straightHenselWidth) := by
          rw [hxAdd]
    _ =
      2 ^
          (profileCheckpoint P.h A.straightHenselStart +
            A.straightHenselWidth) * a := by
        rw [pow_add]
        ring

end AttachedTwoCornerPacket
end MultiCorner
end CSTMicro
end Collatz2
