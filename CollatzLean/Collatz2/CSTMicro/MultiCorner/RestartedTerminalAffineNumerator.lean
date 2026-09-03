import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalGeometryPacket
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileDefectBridge

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
`profileAffineNumerator` の一段右 recurrence。

右端に一列追加すると、既存の prefix はすべて 3 倍され、
新しい右端列の質量 `2 ^ profileCheckpoint h n` が加わる。
-/
theorem profileAffineNumerator_succ_rightAffine
    (h : ℕ → ℕ)
    (n : ℕ) :
    profileAffineNumerator (n + 1) h =
      3 * profileAffineNumerator n h +
        2 ^ profileCheckpoint h n := by
  unfold profileAffineNumerator
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range n)
          (fun k =>
            2 ^ profileCheckpoint h k *
              3 ^ (n + 1 - (k + 1))) =
        3 *
          Finset.sum (Finset.range n)
            (fun k =>
              2 ^ profileCheckpoint h k *
                3 ^ (n - (k + 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < n := Finset.mem_range.mp hk
    have hExp :
        n + 1 - (k + 1) =
          (n - (k + 1)) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  simp

/--
checkpoint が `[b,b+n)` 上で `p+i` という slope-one line なら、
左 prefix を捨てずに exact affine transport が成立する。

これは zero-prefix 仮定を必要としない。
-/
theorem profileAffineNumerator_affineLine_transport
    {b n p : ℕ}
    {h : ℕ → ℕ}
    (hLine :
      ∀ i : ℕ, i < n →
        profileCheckpoint h (b + i) = p + i) :
    profileAffineNumerator (b + n) h + 2 ^ (p + n) =
      3 ^ n * (profileAffineNumerator b h + 2 ^ p) := by
  revert hLine
  induction n with
  | zero =>
      intro _hLine
      simp
  | succ n ih =>
      intro hLine
      have hLinePrefix :
          ∀ i : ℕ, i < n →
            profileCheckpoint h (b + i) = p + i := by
        intro i hi
        exact hLine i (by omega)
      have hIH := ih hLinePrefix
      have hLineLast :
          profileCheckpoint h (b + n) = p + n :=
        hLine n (by omega)
      have hIndex :
          b + (n + 1) = (b + n) + 1 := by
        omega
      have hExp :
          p + (n + 1) = (p + n) + 1 := by
        omega
      calc
        profileAffineNumerator (b + (n + 1)) h +
              2 ^ (p + (n + 1)) =
            3 *
              (profileAffineNumerator (b + n) h +
                2 ^ (p + n)) := by
          rw [hIndex,
            profileAffineNumerator_succ_rightAffine h (b + n),
            hLineLast, hExp, pow_succ]
          ring
        _ = 3 *
              (3 ^ n *
                (profileAffineNumerator b h + 2 ^ p)) := by
          rw [hIH]
        _ = 3 ^ (n + 1) *
              (profileAffineNumerator b h + 2 ^ p) := by
          rw [pow_succ]
          ring

namespace RestartedTerminalGeometryPacket

/--
restarted component `[b,c)` 全体の relative affine transport。

`A_k = profileAffineNumerator k P.h` と書けば、

`A_c + 2^(beattyIndex b - 1 + width)
  = 3^width * (A_b + 2^(beattyIndex b - 1))`

が exact に成立する。
-/
theorem affineNumerator_transport
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    profileAffineNumerator P.terminalCriticalStart P.h +
        2 ^ (beattyIndex S.b - 1 + S.width) =
      3 ^ S.width *
        (profileAffineNumerator S.b P.h +
          2 ^ (beattyIndex S.b - 1)) := by
  have hLine :
      ∀ i : ℕ, i < S.width →
        profileCheckpoint P.h (S.b + i) =
          (beattyIndex S.b - 1) + i := by
    intro i hi
    exact S.checkpoint_offset (by
      rw [S.terminalCriticalStart_eq_b_add_width]
      omega)
  have h :=
    profileAffineNumerator_affineLine_transport
      (b := S.b)
      (n := S.width)
      (p := beattyIndex S.b - 1)
      (h := P.h)
      hLine
  rw [← S.terminalCriticalStart_eq_b_add_width] at h
  exact h

/--
relative affine transport の左端 seed。

これは actual endpoint state から得る Hensel quotient との同一視を
まだ主張しない。現時点では純粋に affine numerator 側の正の量である。
-/
noncomputable def affineSeed
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) : ℕ :=
  profileAffineNumerator S.b P.h +
    2 ^ (beattyIndex S.b - 1)

/-- restarted affine seed は正。 -/
theorem affineSeed_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    0 < S.affineSeed := by
  unfold affineSeed
  positivity

/-- relative affine transport を正の seed で書き直す。 -/
theorem affineNumerator_eq_threePow_mul_affineSeed
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    profileAffineNumerator P.terminalCriticalStart P.h +
        2 ^ (beattyIndex S.b - 1 + S.width) =
      3 ^ S.width * S.affineSeed := by
  simpa [affineSeed] using S.affineNumerator_transport

/--
restarted affine endpoint mass は `3^width` で割り切れる。
quotient は上で定義した正の `affineSeed` そのもの。
-/
theorem threePow_width_dvd_affineEndpointMass
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    3 ^ S.width ∣
      profileAffineNumerator P.terminalCriticalStart P.h +
        2 ^ (beattyIndex S.b - 1 + S.width) := by
  refine ⟨S.affineSeed, ?_⟩
  exact S.affineNumerator_eq_threePow_mul_affineSeed

/--
Shared-Cost の整数算術へ渡すための cast 版 exact transport。
-/
theorem affineEndpointMass_cast_eq_threePow_mul_affineSeed
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    ((profileAffineNumerator P.terminalCriticalStart P.h +
        2 ^ (beattyIndex S.b - 1 + S.width) : ℕ) : ℤ) =
      (3 : ℤ) ^ S.width * (S.affineSeed : ℤ) := by
  exact_mod_cast S.affineNumerator_eq_threePow_mul_affineSeed

end RestartedTerminalGeometryPacket

end MultiCorner
end CSTMicro
end Collatz2
