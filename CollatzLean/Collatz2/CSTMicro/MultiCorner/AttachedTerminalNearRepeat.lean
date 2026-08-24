import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedRepeatIntervalDefectBridge


/-!
# Attached Hensel: terminal-near forced repeat

既存の Beatty factor repeat theorem は任意 base point から始められる。
従って forced window を straight suffix の左端に固定する必要はない。

width `W` と factor length `m` に対し

  offset = W - (2*m+2)

から repeat search を開始すれば、得られる二つの starts は terminal から高々
`2*m+2` 列の帯の中にあり、しかも repeated block 全体は terminal endpoint の
一列手前で止まる。

これは smallness を entrance `M_0` ではなく right-end `M_m` で評価するための
canonical terminal-near window を与える。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
`2*m+2 <= width` なら terminal-near band に length `m` の parallel block が存在する。
-/
theorem exists_terminalNear_sameDeltaOffsetBlock
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      i < j ∧
      j ≤ C.width - (2 * m + 2) + (m + 1) ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let offset := A.straightHenselWidth - (2 * m + 2)
  have hOffset : offset + (2 * m + 2) = A.straightHenselWidth := by
    dsimp [offset]
    exact Nat.sub_add_cancel hWidth
  rcases
      exists_repeated_beattyDisplacementBlock
        (A.straightHenselStart + offset) m with
    ⟨u, v, huv, hvBound, hDisp⟩
  let i := offset + u
  let j := offset + v
  have hij : i < j := by
    dsimp [i, j]
    omega
  have hjEnd : j + m < A.straightHenselWidth := by
    dsimp [j]
    omega
  have hDispGlobal :
      ∀ r : ℕ, r ≤ m →
        beattyIndex (A.straightHenselStart + j + r) -
            beattyIndex (A.straightHenselStart + j) =
          beattyIndex (A.straightHenselStart + i + r) -
            beattyIndex (A.straightHenselStart + i) := by
    intro r hr
    have h := hDisp r hr
    have hJr :
        A.straightHenselStart + j + r =
          (A.straightHenselStart + offset) + v + r := by
      dsimp [j]
      omega
    have hJ :
        A.straightHenselStart + j =
          (A.straightHenselStart + offset) + v := by
      dsimp [j]
      omega
    have hIr :
        A.straightHenselStart + i + r =
          (A.straightHenselStart + offset) + u + r := by
      dsimp [i]
      omega
    have hI :
        A.straightHenselStart + i =
          (A.straightHenselStart + offset) + u := by
      dsimp [i]
      omega
    rw [hJr, hJ, hIr, hI]
    exact h
  let Delta := C.delta j - C.delta i
  have hBlock : C.SameDeltaOffsetBlock i j m Delta := by
    exact
      A.sameDeltaOffsetBlock_of_beattyDisplacementBlock
        hStart (Nat.le_of_lt hij) hjEnd hDispGlobal
  have hWidthOffset :
      C.width - (2 * m + 2) = offset := by
    dsimp [C, offset, toFreeBaseMonotoneHenselChain]
  refine ⟨i, j, Delta, ?_, hij, ?_, ?_, hBlock⟩
  · rw [hWidthOffset]
    dsimp [i]
    omega
  · rw [hWidthOffset]
    dsimp [j]
    exact Nat.add_le_add_left hvBound offset
  · change j + m < A.straightHenselWidth
    exact hjEnd

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
