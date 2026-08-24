import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyFactorRepeat
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselRepeatArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCanonicalHenselBridge

/-!
# Attached Hensel: Beatty factor repeat の free-base 移植

attached canonical bridge で得た straight suffix は、入口指数を固定しない
`FreeBaseMonotoneHenselChain` である。

このファイルでは

* straight suffix の checkpoint が exact に傾き 1 の直線になること、
* actual depth `delta` の relative formula、
* repeated Beatty displacement block から `SameDeltaOffsetBlock` を作ること、
* 十分な room があれば repeated block が actual attached suffix 内に存在すること、

を証明する。

restart 固有の `delta 0 = 1` は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
straight suffix 内の ordinary profile checkpoint は開始 checkpoint から毎回 exact に 1 進む。
-/
theorem straight_profileCheckpoint_eq_base_add
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    profileCheckpoint P.h (A.straightHenselStart + i) =
      profileCheckpoint P.h A.straightHenselStart + i := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      have hiPrev : i < A.straightHenselWidth := by omega
      have hIH := ih hiPrev
      let k := A.straightHenselStart + i
      have hEnd := A.straightHenselStart_add_width
      have hPrev : A.normalForm.previous < k := by
        dsimp [k]
        unfold straightHenselStart
        omega
      have hTerm : k < A.normalForm.terminal := by
        rw [A.terminal_eq]
        dsimp [k] at hEnd ⊢
        omega
      have hGap := A.internal_carryRunGap_eq_one hPrev hTerm
      have hkC : k + 1 < P.terminalCriticalStart := by
        rw [← A.terminal_succ_eq_terminalCriticalStart]
        omega
      rw [carryRunGap_of_succ_lt P hkC] at hGap
      have hcM : P.terminalCriticalStart ≤ P.m :=
        P.terminalCriticalStart_spec.1
      have hStrict :=
        P.admissible.checkpoint_strict
          (k := k)
          (by omega : k + 1 < P.m)
      have hNext :
          profileCheckpoint P.h (k + 1) =
            profileCheckpoint P.h k + 1 := by
        have hPos :
            0 < profileCheckpoint P.h (k + 1) -
              profileCheckpoint P.h k :=
          Nat.sub_pos_of_lt hStrict
        omega
      have hIdx :
          A.straightHenselStart + (i + 1) = k + 1 := by
        dsimp [k]
        omega
      rw [hIdx, hNext]
      rw [hIH]
      omega

/--
straight suffix 内の local index は admissible profile の
relevant interval 内にある。
-/
private theorem straightHenselStart_add_lt_m
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    A.straightHenselStart + i < P.m := by
  have hEnd :=
    A.straightHenselStart_add_width
  have hcM :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  omega

/--
attached straight suffix の actual depth relation を、
Nat subtraction を使わない加法形で表したもの。

  r + delta_(i+r) + beta(start+i)
    = delta_i + beta(start+i+r)

profile checkpoint の defining equality から直接得る
core identity である。
-/
private theorem straightHenselDelta_relative_add_exact
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i r : ℕ}
    (hi : i < A.straightHenselWidth)
    (hir : i + r < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    r + C.delta (i + r) +
        beattyIndex (A.straightHenselStart + i) =
      C.delta i +
        beattyIndex (A.straightHenselStart + i + r) := by
  dsimp
  have hLine0 :=
    A.straight_profileCheckpoint_eq_base_add hi
  have hLineR :=
    A.straight_profileCheckpoint_eq_base_add hir
  have hiM :
      A.straightHenselStart + i < P.m :=
    straightHenselStart_add_lt_m A hi
  have hirM :
      A.straightHenselStart + (i + r) < P.m :=
    straightHenselStart_add_lt_m A hir
  have hDepth0 :=
    P.admissible.depth_le hiM
  have hDepthR :=
    P.admissible.depth_le hirM
  unfold profileCheckpoint at hLine0 hLineR
  -- free-base chain の delta を actual profile depth に戻す。
  change
    r + P.h (A.straightHenselStart + (i + r)) +
        beattyIndex (A.straightHenselStart + i) =
      P.h (A.straightHenselStart + i) +
        beattyIndex (A.straightHenselStart + i + r)
  -- Beatty index の引数を一つの結合形へ揃える。
  have hIdx :
      A.straightHenselStart + (i + r) =
        A.straightHenselStart + i + r := by
    omega
  rw [hIdx] at hLineR hDepthR
  rw [hIdx]
  omega

/--
Beatty index は nonnegative shift に対して減少しない。
-/
private theorem beattyIndex_le_add_right
    (s r : ℕ) :
    beattyIndex s ≤ beattyIndex (s + r) := by
  by_cases hr0 : r = 0
  · subst r
    simp
  · exact
      Nat.le_of_lt
        (beattyIndex_strictMono (by omega))

/--
attached straight suffix の actual depth は Beatty displacement から exact に復元できる。

  r + delta_(i+r)
    = delta_i + (beta(start+i+r)-beta(start+i)).

Nat subtraction を含まない additive core identity を先に取り、
Beatty monotonicity により最後に displacement form へ変換する。
-/
theorem straightHenselDelta_relative_exact
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i r : ℕ}
    (hi : i < A.straightHenselWidth)
    (hir : i + r < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    r + C.delta (i + r) =
      C.delta i +
        (beattyIndex (A.straightHenselStart + i + r) -
          beattyIndex (A.straightHenselStart + i)) := by
  dsimp
  have hAdd :=
    straightHenselDelta_relative_add_exact
      A hStart hi hir
  dsimp at hAdd
  have hBetaMono :
      beattyIndex (A.straightHenselStart + i) ≤
        beattyIndex (A.straightHenselStart + i + r) := by
    have h :=
      beattyIndex_le_add_right
        (A.straightHenselStart + i) r
    simpa [Nat.add_assoc] using h
  simp only [Nat.add_assoc] at hAdd hBetaMono ⊢
  omega

/--
二つの Beatty displacement block が一致すれば、対応する attached depth profile は
一定 offset だけ平行移動する。
-/
theorem sameDeltaOffsetBlock_of_beattyDisplacementBlock
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j m : ℕ}
    (hij : i ≤ j)
    (hjEnd : j + m < A.straightHenselWidth)
    (hDisp :
      ∀ r : ℕ, r ≤ m →
        beattyIndex (A.straightHenselStart + j + r) -
            beattyIndex (A.straightHenselStart + j) =
          beattyIndex (A.straightHenselStart + i + r) -
            beattyIndex (A.straightHenselStart + i)) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let Delta := C.delta j - C.delta i
    C.SameDeltaOffsetBlock i j m Delta := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  have hj : j < C.width := by
    change j < A.straightHenselWidth
    omega
  have hMono : C.delta i ≤ C.delta j :=
    C.delta_mono_of_le hij hj
  intro r hr
  have hiR : i + r < A.straightHenselWidth := by omega
  have hjR : j + r < A.straightHenselWidth := by omega
  have hi0 : i < A.straightHenselWidth := by omega
  have hj0 : j < A.straightHenselWidth := by omega
  have hRelI :=
    A.straightHenselDelta_relative_exact hStart hi0 hiR
  have hRelJ :=
    A.straightHenselDelta_relative_exact hStart hj0 hjR
  dsimp [C] at hMono hRelI hRelJ ⊢
  have hDispR := hDisp r hr
  omega

/--
`2*m+2 <= width` なら terminal endpoint を含めずに、length `m` の parallel block が
actual attached straight suffix 内に必ず存在する。

`+2` は free-base chain の terminal `delta_width = h(c)=0` を repeated block に
混入させないための一列分の余裕である。
-/
theorem exists_sameDeltaOffsetBlock_of_two_mul_add_two_le_width
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      i < j ∧
      j ≤ m + 1 ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta := by
  dsimp
  rcases
      exists_repeated_beattyDisplacementBlock
        A.straightHenselStart m with
    ⟨i, j, hij, hjBound, hDisp⟩
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let Delta := C.delta j - C.delta i
  have hjEndA : j + m < A.straightHenselWidth := by omega
  have hBlock : C.SameDeltaOffsetBlock i j m Delta := by
    exact
      A.sameDeltaOffsetBlock_of_beattyDisplacementBlock
        hStart (Nat.le_of_lt hij) hjEndA hDisp
  refine ⟨i, j, Delta, hij, hjBound, ?_, hBlock⟩
  change j + m < A.straightHenselWidth
  exact hjEndA

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
