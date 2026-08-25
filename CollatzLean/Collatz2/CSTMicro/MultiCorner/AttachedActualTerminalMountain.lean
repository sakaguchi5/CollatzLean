import CollatzLean.Collatz2.Mountain.Block
import CollatzLean.Collatz2.Core.Interval
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalTailDepthCoordinates

/-!
# MultiCorner attached branch: actual terminal mountain

actual odd-only `Runs` の中で attached terminal interval を lossless に切り出し、
その body が

  [1^(W-1), d],   d >= 2

であることが分かっている場合、それを既存 `Word.MountainRun` へ昇格する。

ここで

  W = straightHenselWidth

であり、attached geometry 自身から `0 < W` が従うので、mountain の
`oddRunLength = (W-1)+1` は exact に `W` になる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
lossless interval と whole actual run から terminal body の actual mountain を切り出す。

`hBody` は attached tail の exponent shape を表す。whole run を interval decomposition で
二回 split するため、body の endpoint は existence で回収され、人工的な state を追加しない。
-/
theorem actualTerminalMountain
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {whole : Collatz2.Word}
    {x z d : ℕ}
    (I : Collatz2.Interval whole)
    (hWhole : Collatz2.Runs whole x z)
    (hBody :
      I.body =
        List.replicate (A.straightHenselWidth - 1) 1 ++ [d])
    (hDrop : 2 ≤ d) :
    ∃ xStart xEnd : ℕ,
      ∃ T : Collatz2.Word.MountainRun I.body xStart xEnd,
        T.shape.oddRunLength = A.straightHenselWidth := by
  have hDecomp :
      whole = I.left ++ (I.body ++ I.right) := by
    simpa [List.append_assoc] using I.decomp
  have hWhole' :
      Collatz2.Runs
        (I.left ++ (I.body ++ I.right)) x z := by
    rw [← hDecomp]
    exact hWhole
  obtain ⟨xStart, _hLeft, hTail⟩ :=
    Collatz2.Runs.split_append hWhole'
  obtain ⟨xEnd, hBodyRun, _hRight⟩ :=
    Collatz2.Runs.split_append hTail
  let S : Collatz2.Word.MountainBlock I.body := {
    riseCount := A.straightHenselWidth - 1
    dropExponent := d
    word_eq := hBody
    drop_ge_two := hDrop
  }
  let T : Collatz2.Word.MountainRun I.body xStart xEnd := {
    shape := S
    run := hBodyRun
  }
  refine ⟨xStart, xEnd, T, ?_⟩
  have hWPos := A.straightHenselWidth_pos
  dsimp [T, S, Collatz2.Word.MountainBlock.oddRunLength]
  omega

end AttachedTwoCornerPacket
end MultiCorner
end CSTMicro
end Collatz2
