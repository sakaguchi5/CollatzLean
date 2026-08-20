import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleExposedCornerRigidity

/-!
# Pure B: single-corner terminal core = one shifted critical interval defect

single exposed branch では positive profile support は `[b,c)` で、checkpoints は

  p_k = beta(b)-1 + (k-b).

terminal core

  C = sum_{k<c} (2^beta(k)-2^p_k) 3^(c-k-1)

をこの直線 checkpoint に代入すると

  C = 2^(beta(b)-1)
        * [ 2 Phi[b,c] - (3^(c-b)-2^(c-b)) ].

ここでは subtraction/cast の摩擦を避け、最終 identity を `Int` で固定する。
`Phi[b,c]` は既存 `criticalIntervalPhiZ`。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- closed profile column の signed form。 -/
def profileDyadicClosedColumnZ
    (c : ℕ)
    (h : ℕ → ℕ)
    (k : ℕ) : ℤ :=
  ((2 : ℤ) ^ beattyIndex k -
      (2 : ℤ) ^ (beattyIndex k - h k)) *
    (3 : ℤ) ^ (c - (k + 1))

/-- admissible depth では Nat closed column の cast が signed form と一致。 -/
theorem profileDyadicClosedColumn_cast_eq_Z
    {m c k : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    (hk : k < m) :
    (profileDyadicClosedColumn c k (h k) : ℤ) =
      profileDyadicClosedColumnZ c h k := by
  have hDepth := A.depth_le hk
  have hSubLe : beattyIndex k - h k ≤ beattyIndex k := by omega
  have hPowLe :
      2 ^ (beattyIndex k - h k) ≤ 2 ^ beattyIndex k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hSubLe
  unfold profileDyadicClosedColumn profileDyadicClosedColumnZ
  rw [Nat.cast_mul, Nat.cast_sub hPowLe]
  push_cast
  rfl

/-- terminal core の signed closed-column sum。 -/
theorem terminalCore_cast_eq_sum_closedColumnZ
    (P : PureBProfileObstruction) :
    (P.terminalNoncriticalProfileCore : ℤ) =
      Finset.sum (Finset.range P.terminalCriticalStart)
        (fun k =>
          profileDyadicClosedColumnZ
            P.terminalCriticalStart P.h k) := by
  let c := P.terminalCriticalStart
  have hcLe : c ≤ P.m := P.terminalCriticalStart_spec.1
  unfold PureBProfileObstruction.terminalNoncriticalProfileCore
  unfold profileDyadicClosedNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro k hkMem
  have hkC : k < c := Finset.mem_range.mp hkMem
  exact profileDyadicClosedColumn_cast_eq_Z
    P.admissible (lt_of_lt_of_le hkC hcLe)

/-- elementary `2/3` geometric telescope。 -/
theorem twoThree_geometricSumZ
    (n : ℕ) :
    Finset.sum (Finset.range n)
        (fun i => (2 : ℤ) ^ i * (3 : ℤ) ^ (n - 1 - i)) =
      (3 : ℤ) ^ n - (2 : ℤ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hPrefix :
          Finset.sum (Finset.range n)
              (fun i =>
                (2 : ℤ) ^ i *
                  (3 : ℤ) ^ (n + 1 - 1 - i)) =
            3 *
              Finset.sum (Finset.range n)
                (fun i =>
                  (2 : ℤ) ^ i *
                    (3 : ℤ) ^ (n - 1 - i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < n := Finset.mem_range.mp hi
        have hExp : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
        rw [hExp, pow_succ]
        ring
      rw [hPrefix, ih]
      have hLast : n + 1 - 1 - n = 0 := by omega
      rw [hLast, pow_zero]
      rw [show n + 1 = Nat.succ n by rfl, pow_succ, pow_succ]
      ring

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- single-corner interval の left Beatty height は positive。 -/
theorem beatty_b_pos
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    0 < beattyIndex S.b := by
  have hcLe : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m := lt_of_lt_of_le S.b_lt_c hcLe
  have hDepth := P.admissible.depth_le hbM
  rw [S.h_b_eq_one] at hDepth
  omega

/--
main single-corner closed form。
-/
theorem terminalCore_eq_shiftedCriticalInterval
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    (P.terminalNoncriticalProfileCore : ℤ) =
      (2 : ℤ) ^ (beattyIndex S.b - 1) *
        (2 * criticalIntervalPhiZ S.b P.terminalCriticalStart -
          ((3 : ℤ) ^ (P.terminalCriticalStart - S.b) -
            (2 : ℤ) ^ (P.terminalCriticalStart - S.b))) := by
  let b := S.b
  let c := P.terminalCriticalStart
  let n := c - b
  let f : ℕ → ℤ :=
    fun k => profileDyadicClosedColumnZ c P.h k
  have hbLtC : b < c := by simpa [b, c] using S.b_lt_c
  have hbLeC : b ≤ c := Nat.le_of_lt hbLtC
  have hcLeM : c ≤ P.m := P.terminalCriticalStart_spec.1
  have hbM : b < P.m := lt_of_lt_of_le hbLtC hcLeM
  have hBetaBPos : 0 < beattyIndex b := by
    simpa [b] using S.beatty_b_pos
  have hcEq : c = b + n := by
    dsimp [n]
    omega
  have hPrefixZero :
      Finset.sum (Finset.range b) f = 0 := by
    apply Finset.sum_eq_zero
    intro k hkMem
    have hkb : k < b := Finset.mem_range.mp hkMem
    have hkM : k < P.m := lt_trans hkb hbM
    have hZero :=
      S.depth_eq_zero_of_outside hkM (Or.inl hkb)
    unfold profileDyadicClosedColumnZ
    rw [hZero]
    simp
  have hCoreOffset :
      (P.terminalNoncriticalProfileCore : ℤ) =
        Finset.sum (Finset.range n)
          (fun i => f (b + i)) := by
    calc
      (P.terminalNoncriticalProfileCore : ℤ)
          = Finset.sum (Finset.range c) f := by
              simpa [f, c] using terminalCore_cast_eq_sum_closedColumnZ P
      _ =
          Finset.sum (Finset.range b) f +
            Finset.sum (Finset.range n) (fun i => f (b + i)) := by
              rw [hcEq, Finset.sum_range_add]
      _ = Finset.sum (Finset.range n) (fun i => f (b + i)) := by
              rw [hPrefixZero, zero_add]
  have hCoreTerms :
      (P.terminalNoncriticalProfileCore : ℤ) =
        Finset.sum (Finset.range n)
          (fun i =>
            ((2 : ℤ) ^ beattyIndex (b + i) -
              (2 : ℤ) ^ (beattyIndex b - 1 + i)) *
              (3 : ℤ) ^ (c - (b + i + 1))) := by
    rw [hCoreOffset]
    apply Finset.sum_congr rfl
    intro i hiMem
    have hiN : i < n := Finset.mem_range.mp hiMem
    have hbiC : b + i < c := by
      dsimp [n] at hiN
      omega
    have hCheckpoint :=
      S.checkpoint_line (b + i) (by omega) (by simpa [c] using hbiC)
    dsimp [f]
    unfold profileDyadicClosedColumnZ
    have hSecond :
        beattyIndex (b + i) - P.h (b + i) =
          beattyIndex b - 1 + i := by
      simpa [profileCheckpoint, b] using hCheckpoint
    rw [hSecond]
  have hFirstSum :
      Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^ beattyIndex (b + i) *
              (3 : ℤ) ^ (c - (b + i + 1))) =
        (2 : ℤ) ^ beattyIndex b * criticalIntervalPhiZ b c := by
    unfold criticalIntervalPhiZ
    rw [CriticalRecordPiece.sum_Ico_eq_sum_range_sub_public
      (fun k =>
        (2 : ℤ) ^ (beattyIndex k - beattyIndex b) *
          (3 : ℤ) ^ (c - 1 - k)) hbLeC]
    dsimp [n]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hiMem
    have hBetaMono : beattyIndex b ≤ beattyIndex (b + i) := by
      by_cases hi0 : i = 0
      · subst i
        exact le_rfl
      · exact le_of_lt (beattyIndex_strictMono (by omega))
    have hBeta :
        beattyIndex (b + i) =
          beattyIndex b + (beattyIndex (b + i) - beattyIndex b) := by
      omega
    have hThree : c - (b + i + 1) = c - 1 - (b + i) := by omega
    rw [hBeta, pow_add, hThree]
    ring_nf
    simp
  have hSecondSum :
      Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^ (beattyIndex b - 1 + i) *
              (3 : ℤ) ^ (c - (b + i + 1))) =
        (2 : ℤ) ^ (beattyIndex b - 1) *
          ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
    calc
      Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^ (beattyIndex b - 1 + i) *
              (3 : ℤ) ^ (c - (b + i + 1)))
          =
        (2 : ℤ) ^ (beattyIndex b - 1) *
          Finset.sum (Finset.range n)
            (fun i =>
              (2 : ℤ) ^ i * (3 : ℤ) ^ (n - 1 - i)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hiMem
              have hiN : i < n := Finset.mem_range.mp hiMem
              have hThree : c - (b + i + 1) = n - 1 - i := by
                dsimp [n]
                omega
              rw [pow_add, hThree]
              ring
      _ =
        (2 : ℤ) ^ (beattyIndex b - 1) *
          ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
            rw [twoThree_geometricSumZ]
  have hDifference :
      (P.terminalNoncriticalProfileCore : ℤ) =
        (2 : ℤ) ^ beattyIndex b * criticalIntervalPhiZ b c -
          (2 : ℤ) ^ (beattyIndex b - 1) *
            ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
    calc
      (P.terminalNoncriticalProfileCore : ℤ)
          =
        Finset.sum (Finset.range n)
          (fun i =>
            ((2 : ℤ) ^ beattyIndex (b + i) -
              (2 : ℤ) ^ (beattyIndex b - 1 + i)) *
              (3 : ℤ) ^ (c - (b + i + 1))) := hCoreTerms
      _ =
        Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^ beattyIndex (b + i) *
              (3 : ℤ) ^ (c - (b + i + 1))) -
        Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^ (beattyIndex b - 1 + i) *
              (3 : ℤ) ^ (c - (b + i + 1))) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ =
        (2 : ℤ) ^ beattyIndex b * criticalIntervalPhiZ b c -
          (2 : ℤ) ^ (beattyIndex b - 1) *
            ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
              rw [hFirstSum, hSecondSum]
  have hBetaPred : beattyIndex b = (beattyIndex b - 1) + 1 := by omega
  rw [hDifference, hBetaPred, pow_add]
  norm_num
  dsimp [b, c, n]
  ring

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
