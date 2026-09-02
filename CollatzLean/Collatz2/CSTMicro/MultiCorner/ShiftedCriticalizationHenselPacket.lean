import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalGeometryPacket
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationUnitStartState
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreValuation
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileDefectBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain

/-!
# MultiCorner: shifted criticalization Hensel packet

hard Case II の restarted 側では

  previous < b ≤ s := criticalizationStart < c := terminalCriticalStart

となる。Case I の Hensel chain は `b` から始まり initial delta が `1` だったが、
Case II で arithmetic divisibility が保証されるのは `s` から右だけである。

そこでこのファイルでは chain を `s` へ shift して作り直す。

主な exact identity は次の通り。

(2)  U = N_s + 2^p_s qH_s

(3)  U = 3^s (y-q) + Psi(s) - 2^beta(s) Z_s
     （既存 theorem の wrapper）

(4)  2^p_s qH_s
       = 3^s (y-q) + A_s - 2^beta(s) Z_s

(5)  qH_s = X_s - 2^h(s) Z_s
     ここでは X_s を (4) の affine equation で canonical に定義する。

(6)  s<c なので qH_s>0、従って X_s > 2^h(s) Z_s。

(8)  critical shadow は s-1 へ integral に延長できない。

注意: 前段の議論で式 (7) と呼んだ

  3 D_(s-1) = 2 D_s + 2^h(s-1) - 1

を actual orbit state の式として使うには、`X_s` を actual prefix trace state と同定する
追加 bridge が必要である。このファイルではそこを暗黙に仮定しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
hard Case II の shifted Hensel geometry。

`b ≤ s < c` を明示し、Case I の `s ≤ previous` は持たない。
-/
structure ShiftedCriticalizationHenselPacket
    (P : PureBProfileObstruction)
    (N : LastTwoExposedNormalForm P) where
  geometry : RestartedTerminalGeometryPacket P N
  hStart : 0 < P.criticalizationStart
  b_le_criticalization : geometry.b ≤ P.criticalizationStart
  criticalization_lt_terminal :
    P.criticalizationStart < P.terminalCriticalStart

namespace ShiftedCriticalizationHenselPacket

/--
raw last-two geometry から hard Case II の shifted packet を直接作る constructor。

`hBLe` が hard side `b ≤ s`、`hStartLtTerminal` が nonempty shifted suffix を表す。
-/
theorem of_lastTwo
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P)
    (hTerminal : N.terminal = P.terminalCriticalStart - 1)
    (hcPos : 0 < P.terminalCriticalStart)
    (hRestart : P.h (N.previous + 1) = 0)
    (hStart : 0 < P.criticalizationStart)
    (hBLe : restartedComponentStart N ≤ P.criticalizationStart)
    (hStartLtTerminal :
      P.criticalizationStart < P.terminalCriticalStart) :
    ShiftedCriticalizationHenselPacket P N := by
  let G : RestartedTerminalGeometryPacket P N := {
    terminal_eq := hTerminal
    terminalCriticalStart_pos := hcPos
    restart_zero := hRestart
  }
  refine {
    geometry := G
    hStart := hStart
    b_le_criticalization := ?_
    criticalization_lt_terminal := hStartLtTerminal
  }
  simpa [RestartedTerminalGeometryPacket.b, G] using hBLe

/-- `s` から `c` までの shifted width。 -/
noncomputable def width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (_S : ShiftedCriticalizationHenselPacket P N) : ℕ :=
  P.terminalCriticalStart - P.criticalizationStart

/-- shifted width は正。 -/
theorem width_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    0 < S.width := by
  unfold width
  exact Nat.sub_pos_iff_lt.mpr S.criticalization_lt_terminal

/-- terminal start は `s + shifted width`。 -/
theorem terminalCriticalStart_eq_start_add_width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    P.terminalCriticalStart = P.criticalizationStart + S.width := by
  unfold width
  exact
    (Nat.add_sub_of_le
      (Nat.le_of_lt S.criticalization_lt_terminal)).symm

/-- offset `i` の checkpoint exponent。 -/
noncomputable def base
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (_S : ShiftedCriticalizationHenselPacket P N)
    (i : ℕ) : ℕ :=
  profileCheckpoint P.h (P.criticalizationStart + i)

/-- offset `i` の profile depth。Hensel forcing exponent そのもの。 -/
noncomputable def delta
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (_S : ShiftedCriticalizationHenselPacket P N)
    (i : ℕ) : ℕ :=
  P.h (P.criticalizationStart + i)

/-- normalized forcing `2^delta - 1`。 -/
noncomputable def forcing
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    (i : ℕ) : ℤ :=
  (2 : ℤ) ^ S.delta i - 1

/-- shifted component 上では checkpoint base は一列ごとに exact に一つ増える。 -/
theorem base_add
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i r : ℕ}
    (hir : i + r < S.width) :
    S.base (i + r) = S.base i + r := by
  have hcEq := S.terminalCriticalStart_eq_start_add_width
  have hbLeStart :
      S.geometry.b ≤ P.criticalizationStart :=
    S.b_le_criticalization
  have hiC :
      P.criticalizationStart + i <
        P.terminalCriticalStart := by
    rw [hcEq]
    omega
  have hirC :
      P.criticalizationStart + (i + r) <
        P.terminalCriticalStart := by
    rw [hcEq]
    omega
  have hLine0 :=
    S.geometry.checkpoint_line
      (k := P.criticalizationStart + i)
      (by omega)
      hiC
  have hLine1 :=
    S.geometry.checkpoint_line
      (k := P.criticalizationStart + (i + r))
      (by omega)
      hirC
  unfold base
  rw [hLine0, hLine1]
  omega

/-- occupied shifted offset では depth は正。 -/
theorem delta_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i : ℕ}
    (hi : i < S.width) :
    0 < S.delta i := by
  have hcEq := S.terminalCriticalStart_eq_start_add_width
  have hbLeStart :
      S.geometry.b ≤ P.criticalizationStart :=
    S.b_le_criticalization
  unfold delta
  apply S.geometry.support_pos
  · exact le_trans hbLeStart (Nat.le_add_right _ _)
  · rw [hcEq]
    omega

/-- occupied offset の forcing は strict positive。 -/
theorem forcing_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i : ℕ}
    (hi : i < S.width) :
    0 < S.forcing i := by
  have hd : 0 < S.delta i := S.delta_pos hi
  obtain ⟨d, hdEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  unfold forcing
  rw [hdEq, pow_succ]
  have hp : 0 < (2 : ℤ) ^ d := by positivity
  have hpOne : 1 ≤ (2 : ℤ) ^ d := by omega
  nlinarith

/--
一列の rightmost mass は checkpoint の 2 冪と depth forcing に exact 分解する。
-/
theorem rightmostColumnMass_eq_pow_base_mul_forcing
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i : ℕ}
    (hi : i < S.width) :
    (profileRightmostColumnMass P.h (P.criticalizationStart + i) : ℤ) =
      (2 : ℤ) ^ S.base i * S.forcing i := by
  let k := P.criticalizationStart + i
  have hcEq := S.terminalCriticalStart_eq_start_add_width
  have hkC : k < P.terminalCriticalStart := by
    dsimp [k]
    rw [hcEq]
    omega
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k < P.m := lt_of_lt_of_le hkC hcLeM
  have hDepth : P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hkM
  have hExp :
      beattyIndex k = profileCheckpoint P.h k + P.h k := by
    unfold profileCheckpoint
    omega
  have hPowLe :
      2 ^ profileCheckpoint P.h k ≤ 2 ^ beattyIndex k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
  unfold profileRightmostColumnMass base forcing delta
  change
    ((2 ^ beattyIndex k - 2 ^ profileCheckpoint P.h k : ℕ) : ℤ) =
      (2 : ℤ) ^ profileCheckpoint P.h k *
        ((2 : ℤ) ^ P.h k - 1)
  rw [Nat.cast_sub hPowLe]
  push_cast
  rw [hExp, pow_add]
  ring

/--
offset `i+r` の mass を offset `i` の共通 2 冪で括った形。
-/
theorem rightmostColumnMass_eq_pow_base_mul_shifted_term
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i r : ℕ}
    (hir : i + r < S.width) :
    (profileRightmostColumnMass P.h
        (P.criticalizationStart + i + r) : ℤ) =
      (2 : ℤ) ^ S.base i *
        (2 : ℤ) ^ r * S.forcing (i + r) := by
  have hMass :=
    S.rightmostColumnMass_eq_pow_base_mul_forcing
      (i := i + r) hir
  have hBase := S.base_add (i := i) (r := r) hir
  have hIdx :
      P.criticalizationStart + (i + r) =
        P.criticalizationStart + i + r := by omega
  rw [hIdx] at hMass
  rw [hMass, hBase, pow_add]

/--
shifted tail から共通 dyadic base を除いた integer Hensel unit。
-/
noncomputable def unit
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    (i : ℕ) : ℕ → ℤ
  | 0 => 0
  | r + 1 =>
      3 * S.unit i r +
        (2 : ℤ) ^ r * S.forcing (i + r)

@[simp] theorem unit_zero
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    (i : ℕ) :
    S.unit i 0 = 0 := rfl

/-- unit の forward recurrence。 -/
theorem unit_succ
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    (i r : ℕ) :
    S.unit i (r + 1) =
      3 * S.unit i r +
        (2 : ℤ) ^ r * S.forcing (i + r) := rfl

/-- unit を左端 forcing と残り suffix に分ける recurrence。 -/
theorem unit_left_rec
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    (i r : ℕ) :
    S.unit i (r + 1) =
      (3 : ℤ) ^ r * S.forcing i +
        2 * S.unit (i + 1) r := by
  induction r with
  | zero =>
      simp [unit_succ]
  | succ r ih =>
      rw [unit_succ S i (r + 1)]
      rw [ih]
      rw [unit_succ S (i + 1) r]
      have hIdx : i + (r + 1) = (i + 1) + r := by omega
      rw [hIdx, pow_succ]
      ring

/--
shifted closed tail は common dyadic base と `unit` の積に exact 分解する。
-/
theorem restartedClosedTailZ_eq_pow_base_mul_unit
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i r : ℕ}
    (hir : i + r ≤ S.width) :
    restartedClosedTailZ P
        (P.criticalizationStart + i)
        (P.criticalizationStart + i + r) =
      (2 : ℤ) ^ S.base i * S.unit i r := by
  induction r with
  | zero =>
      simp [restartedClosedTailZ]
  | succ r ih =>
      have hirPrev : i + r ≤ S.width := by omega
      have hirMass : i + r < S.width := by omega
      have hIH := ih hirPrev
      have hTailRec :=
        restartedClosedTailZ_succ P
          (b := P.criticalizationStart + i)
          (c := P.criticalizationStart + i + r)
          (by omega)
      have hIndex :
          P.criticalizationStart + i + r + 1 =
            P.criticalizationStart + i + (r + 1) := by
        omega
      rw [hIndex] at hTailRec
      have hMass :=
        S.rightmostColumnMass_eq_pow_base_mul_shifted_term
          (i := i) (r := r) hirMass
      rw [hTailRec, hMass, hIH, unit_succ]
      ring

/-- shifted unit は local width 全体の 3 冪で割れる。 -/
theorem unit_threePow_dvd
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i : ℕ}
    (hi : i ≤ S.width) :
    (3 : ℤ) ^ (S.width - i) ∣
      S.unit i (S.width - i) := by
  have hcEq := S.terminalCriticalStart_eq_start_add_width
  have hsk :
      P.criticalizationStart ≤ P.criticalizationStart + i := by omega
  have hkc :
      P.criticalizationStart + i ≤ P.terminalCriticalStart := by
    rw [hcEq]
    omega
  have hDeep :=
    restartedTail_localWidth_dvd P S.hStart hsk hkc
  have hExp :
      P.terminalCriticalStart - (P.criticalizationStart + i) =
        S.width - i := by
    rw [hcEq]
    omega
  rw [hExp] at hDeep
  have hFactor :=
    S.restartedClosedTailZ_eq_pow_base_mul_unit
      (i := i) (r := S.width - i) (by omega)
  have hEnd :
      P.criticalizationStart + i + (S.width - i) =
        P.terminalCriticalStart := by
    rw [hcEq]
    omega
  rw [hEnd] at hFactor
  rw [hFactor] at hDeep
  exact MonotoneSuffixHenselChain.threePow_dvd_cancel_twoPow hDeep

/-- full shifted divisibility から選ぶ Hensel quotient。 -/
noncomputable def quotient
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    (i : ℕ) : ℤ :=
  if hi : i ≤ S.width then
    Classical.choose (S.unit_threePow_dvd hi)
  else
    0

/-- quotient の defining equation。 -/
theorem quotient_spec
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i : ℕ}
    (hi : i ≤ S.width) :
    S.unit i (S.width - i) =
      (3 : ℤ) ^ (S.width - i) * S.quotient i := by
  unfold quotient
  simp only [dite_eq_left hi]
  exact Classical.choose_spec (S.unit_threePow_dvd hi)

/-- terminal empty suffix の quotient は `0`。 -/
theorem quotient_terminal
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    S.quotient S.width = 0 := by
  have hSpec := S.quotient_spec (i := S.width) le_rfl
  have hSpec' := hSpec.symm
  simpa [unit] using hSpec'

/--
隣接 shifted quotient は pure Hensel recurrence を exact に満たす。

  3 q_i = 2 q_(i+1) + (2^delta_i - 1).
-/
theorem quotient_recurrence
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i : ℕ}
    (hi : i < S.width) :
    3 * S.quotient i =
      2 * S.quotient (i + 1) + S.forcing i := by
  let r : ℕ := S.width - (i + 1)
  have hiLe : i ≤ S.width := by omega
  have hi1Le : i + 1 ≤ S.width := by omega
  have hSplit : S.width - i = r + 1 := by
    dsimp [r]
    omega
  have hQi := S.quotient_spec (i := i) hiLe
  have hQnext := S.quotient_spec (i := i + 1) hi1Le
  have hQi' :
      S.unit i (r + 1) =
        (3 : ℤ) ^ (r + 1) * S.quotient i := by
    rw [← hSplit]
    exact hQi
  have hQnext' :
      S.unit (i + 1) r =
        (3 : ℤ) ^ r * S.quotient (i + 1) := by
    simpa [r] using hQnext
  have hG := S.unit_left_rec i r
  rw [hQi', hQnext'] at hG
  rw [pow_succ] at hG
  have hZero :
      (3 : ℤ) ^ r *
          (3 * S.quotient i - S.forcing i -
            2 * S.quotient (i + 1)) = 0 := by
    calc
      (3 : ℤ) ^ r *
          (3 * S.quotient i - S.forcing i -
            2 * S.quotient (i + 1)) =
        ((3 : ℤ) ^ r * 3) * S.quotient i -
          ((3 : ℤ) ^ r * S.forcing i +
            2 * ((3 : ℤ) ^ r * S.quotient (i + 1))) := by ring
      _ = 0 := by
        rw [hG]
        ring
  have hPowNe : (3 : ℤ) ^ r ≠ 0 := by positivity
  have hCore :
      3 * S.quotient i - S.forcing i -
          2 * S.quotient (i + 1) = 0 := by
    exact (mul_eq_zero.mp hZero).resolve_left hPowNe
  linarith

/-- unit は意味のある区間では非負。 -/
theorem unit_nonneg
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i r : ℕ}
    (hir : i + r ≤ S.width) :
    0 ≤ S.unit i r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hPrev : i + r ≤ S.width := by omega
      have hOcc : i + r < S.width := by omega
      have hIH := ih hPrev
      have hForce : 0 < S.forcing (i + r) := S.forcing_pos hOcc
      rw [unit_succ]
      have hPow : 0 < (2 : ℤ) ^ r := by positivity
      have hTerm :
          0 < (2 : ℤ) ^ r * S.forcing (i + r) :=
        mul_pos hPow hForce
      nlinarith

/-- nonempty unit は strict positive。 -/
theorem unit_pos_of_pos_length
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N)
    {i r : ℕ}
    (hr : 0 < r)
    (hir : i + r ≤ S.width) :
    0 < S.unit i r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hPrev : i + t ≤ S.width := by omega
  have hOcc : i + t < S.width := by omega
  have hNonneg := S.unit_nonneg (i := i) (r := t) hPrev
  have hForce := S.forcing_pos (i := i + t) hOcc
  rw [unit_succ]
  have hPow : 0 < (2 : ℤ) ^ t := by positivity
  have hTerm :
      0 < (2 : ℤ) ^ t * S.forcing (i + t) :=
    mul_pos hPow hForce
  nlinarith

/--
shifted chain の最左 quotient `qH_s` は strict positive。
これが hard Case II の state separation の符号を与える。
-/
theorem quotient_zero_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    0 < S.quotient 0 := by
  have hUnitPos : 0 < S.unit 0 S.width :=
    S.unit_pos_of_pos_length S.width_pos (by omega)
  have hSpec := S.quotient_spec (i := 0) (by omega)
  simp only [Nat.sub_zero] at hSpec
  rw [hSpec] at hUnitPos
  have hPow : 0 < (3 : ℤ) ^ S.width := by positivity
  nlinarith

/-! ## criticalization unit との exact bridge -/

/--
terminal core は shifted width の 3 冪と criticalization unit の積。
-/
theorem terminalCore_eq_threePow_width_mul_criticalizationUnit
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    (P.terminalNoncriticalProfileCore : ℤ) =
      (3 : ℤ) ^ S.width * criticalizationUnit P S.hStart := by
  have hCore := P.profileNumerator_cast_eq_threePow_mul_terminalCore
  have hUnit := profileNumerator_eq_threePow_mul_criticalizationUnit P S.hStart
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hsLeC : P.criticalizationStart ≤ P.terminalCriticalStart :=
    Nat.le_of_lt S.criticalization_lt_terminal
  have hExp :
      P.m - P.criticalizationStart =
        (P.m - P.terminalCriticalStart) + S.width := by
    unfold width
    omega
  have hEq :
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ) =
        (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          ((3 : ℤ) ^ S.width * criticalizationUnit P S.hStart) := by
    calc
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ)
          = (profileDyadicCellNumerator P.m P.h : ℤ) := hCore.symm
      _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          criticalizationUnit P S.hStart := hUnit
      _ =
        (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          ((3 : ℤ) ^ S.width * criticalizationUnit P S.hStart) := by
            rw [hExp, pow_add]
            ring
  have hPowNe :
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) ≠ 0 := by positivity
  exact mul_left_cancel₀ hPowNe hEq

/-- terminal core を cut `s` で prefix と shifted tail に分ける。 -/
theorem terminalCore_eq_scaled_startPrefix_add_shiftedTail
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    (P.terminalNoncriticalProfileCore : ℤ) =
      (3 : ℤ) ^ S.width *
          (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
        restartedClosedTailZ P
          P.criticalizationStart P.terminalCriticalStart := by
  have hSplit :=
    profileDyadicClosedNumerator_cast_eq_scaledPrefix_add_restartedTail
      P (b := P.criticalizationStart) (c := P.terminalCriticalStart)
  simpa [PureBProfileObstruction.terminalNoncriticalProfileCore, width] using hSplit

/--
(2) criticalization unit の exact split。

  U = N_s + 2^p_s qH_s.
-/
theorem criticalizationUnit_eq_startPrefix_add_pow_mul_quotient
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    criticalizationUnit P S.hStart =
      (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
        (2 : ℤ) ^ S.base 0 * S.quotient 0 := by
  have hCoreUnit :=
    S.terminalCore_eq_threePow_width_mul_criticalizationUnit
  have hCoreSplit :=
    S.terminalCore_eq_scaled_startPrefix_add_shiftedTail
  have hTail :=
    S.restartedClosedTailZ_eq_pow_base_mul_unit
      (i := 0) (r := S.width) (by omega)
  have hcEq := S.terminalCriticalStart_eq_start_add_width
  have hEnd :
      P.criticalizationStart + 0 + S.width =
        P.terminalCriticalStart := by
    rw [hcEq]
    simp
  rw [hEnd] at hTail
  simp only [Nat.add_zero] at hTail
  have hQ := S.quotient_spec (i := 0) (by omega)
  simp only [Nat.sub_zero] at hQ
  have hCoreExpanded :
      (P.terminalNoncriticalProfileCore : ℤ) =
        (3 : ℤ) ^ S.width *
          ((profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
            (2 : ℤ) ^ S.base 0 * S.quotient 0) := by
    calc
      (P.terminalNoncriticalProfileCore : ℤ)
          =
        (3 : ℤ) ^ S.width *
            (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
          restartedClosedTailZ P
            P.criticalizationStart P.terminalCriticalStart := hCoreSplit
      _ =
        (3 : ℤ) ^ S.width *
            (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
          (2 : ℤ) ^ S.base 0 * S.unit 0 S.width := by
            rw [hTail]
      _ =
        (3 : ℤ) ^ S.width *
          ((profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
            (2 : ℤ) ^ S.base 0 * S.quotient 0) := by
            rw [hQ]
            ring
  have hScaled :
      (3 : ℤ) ^ S.width * criticalizationUnit P S.hStart =
        (3 : ℤ) ^ S.width *
          ((profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) +
            (2 : ℤ) ^ S.base 0 * S.quotient 0) := by
    rw [← hCoreUnit, hCoreExpanded]
  have hPowNe : (3 : ℤ) ^ S.width ≠ 0 := by positivity
  exact mul_left_cancel₀ hPowNe hScaled

/--
(3) 既存 start-state identity を shifted packet から直接読む wrapper。
-/
theorem criticalizationUnit_eq_startState
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    criticalizationUnit P S.hStart =
      (3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
        criticalPrefixPhiZ P.criticalizationStart -
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
          P.criticalizationStartStateInt :=
  criticalizationUnit_eq_start_state_expression P S.hStart

/-- cut `s` の affine numerator と closed dyadic mass の和は critical numerator。 -/
theorem startAffine_add_startClosed_eq_criticalPrefix
    {P : PureBProfileObstruction} :
    (profileAffineNumerator P.criticalizationStart P.h : ℤ) +
        (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) =
      criticalPrefixPhiZ P.criticalizationStart := by
  have hRoof :
      ∀ k : ℕ, k < P.criticalizationStart →
        P.h k ≤ beattyIndex k := by
    intro k hk
    apply P.admissible.depth_le
    have hsLeM : P.criticalizationStart ≤ P.m :=
      P.criticalizationStart_spec.1
    omega
  have hNat :=
    profileAffineNumerator_add_profileDyadicClosedNumerator_eq_criticalPrefixPhiNat
      hRoof
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hZ
  rw [criticalPrefixPhiNat_cast_eq_criticalPrefixPhiZ] at hZ
  exact hZ

/-- (4) shifted Hensel quotient と critical shadow の exact affine bridge。 -/
theorem pow_mul_quotient_eq_affine_sub_shadow
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    (2 : ℤ) ^ S.base 0 * S.quotient 0 =
      (3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
        (profileAffineNumerator P.criticalizationStart P.h : ℤ) -
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
          P.criticalizationStartStateInt := by
  have hSplit :=
    S.criticalizationUnit_eq_startPrefix_add_pow_mul_quotient
  have hStart :=
    S.criticalizationUnit_eq_startState
  have hPrefix :
      (profileAffineNumerator P.criticalizationStart P.h : ℤ) +
          (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) =
        criticalPrefixPhiZ P.criticalizationStart :=
    startAffine_add_startClosed_eq_criticalPrefix
  calc
    (2 : ℤ) ^ S.base 0 * S.quotient 0
        =
      criticalizationUnit P S.hStart -
        (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) := by
          rw [hSplit]
          ring
    _ =
      ((3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
          criticalPrefixPhiZ P.criticalizationStart -
          (2 : ℤ) ^ beattyIndex P.criticalizationStart *
            P.criticalizationStartStateInt) -
        (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) := by
          rw [hStart]
    _ =
      (3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
        (profileAffineNumerator P.criticalizationStart P.h : ℤ) -
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
          P.criticalizationStartStateInt := by
          rw [← hPrefix]
          ring

/--
(5) の右辺に現れる affine state を canonical に定義する。

後段で actual prefix trace state と同定する対象であり、この定義自体は actuality を仮定しない。
-/
noncomputable def affineStateAtCriticalization
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) : ℤ :=
  S.quotient 0 +
    (2 : ℤ) ^ P.h P.criticalizationStart *
      P.criticalizationStartStateInt

/--
(5) quotient は affine state と critical shadow の差そのもの。
-/
theorem quotient_eq_affineState_sub_scaledShadow
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    S.quotient 0 =
      S.affineStateAtCriticalization -
        (2 : ℤ) ^ P.h P.criticalizationStart *
          P.criticalizationStartStateInt := by
  unfold affineStateAtCriticalization
  ring

/--
上の affine state は cut `s` の affine numerator equation を exact に満たす。

  2^p_s X_s = 3^s (y-q) + A_s.
-/
theorem pow_base_mul_affineState_eq_affineNumerator
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    (2 : ℤ) ^ S.base 0 * S.affineStateAtCriticalization =
      (3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
        (profileAffineNumerator P.criticalizationStart P.h : ℤ) := by
  have hBridge := S.pow_mul_quotient_eq_affine_sub_shadow
  have hsLtM : P.criticalizationStart < P.m := by
    exact lt_of_lt_of_le
      S.criticalization_lt_terminal
      P.terminalCriticalStart_spec.1
  have hDepth :
      P.h P.criticalizationStart ≤ beattyIndex P.criticalizationStart :=
    P.admissible.depth_le hsLtM
  have hBeta :
      beattyIndex P.criticalizationStart =
        S.base 0 + P.h P.criticalizationStart := by
    unfold base profileCheckpoint
    simp only [Nat.add_zero]
    omega
  rw [hBeta, pow_add] at hBridge
  unfold affineStateAtCriticalization
  calc
    (2 : ℤ) ^ S.base 0 *
        (S.quotient 0 +
          (2 : ℤ) ^ P.h P.criticalizationStart *
            P.criticalizationStartStateInt)
        =
      (2 : ℤ) ^ S.base 0 * S.quotient 0 +
        ((2 : ℤ) ^ S.base 0 *
          (2 : ℤ) ^ P.h P.criticalizationStart) *
            P.criticalizationStartStateInt := by ring
    _ =
      (3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
        (profileAffineNumerator P.criticalizationStart P.h : ℤ) := by
          linarith

/--
(6) hard Case II の strict state separation。

  X_s > 2^h(s) Z_s.
-/
theorem scaledShadow_lt_affineStateAtCriticalization
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    (2 : ℤ) ^ P.h P.criticalizationStart *
        P.criticalizationStartStateInt <
      S.affineStateAtCriticalization := by
  have hQ : 0 < S.quotient 0 := S.quotient_zero_pos
  unfold affineStateAtCriticalization
  linarith

/-! ## 左延長不能性 -/

/-- critical shadow を一段左へ延長するために必要な residue。 -/
noncomputable def leftExtensionResidue
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (_S : ShiftedCriticalizationHenselPacket P N) : ℤ :=
  (2 : ℤ) ^
      (beattyIndex P.criticalizationStart -
        beattyIndex (P.criticalizationStart - 1)) *
    P.criticalizationStartStateInt - 1

/--
(8) criticalization の最小性により、左延長 residue は 3 で割れない。
-/
theorem leftExtensionResidue_not_three_dvd
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) :
    ¬ (3 : ℤ) ∣ S.leftExtensionResidue := by
  unfold leftExtensionResidue
  exact P.criticalizationStart_pred_not_integral_residue S.hStart

/--
式 (7) を actual difference recurrence として使うために残る bridge を明示するための predicate。

`X_s` が actual prefix state であり、その一段左 state `X_(s-1)` と
`2 X_s = 3 X_(s-1) + 1` を満たすことを後段で供給すれば、
`leftExtensionResidue_not_three_dvd` を Hensel predecessor の延長不能性へ翻訳できる。
-/
def HasActualLeftStepBridge
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : ShiftedCriticalizationHenselPacket P N) : Prop :=
  ∃ Xpred : ℤ,
    2 * S.affineStateAtCriticalization = 3 * Xpred + 1

end ShiftedCriticalizationHenselPacket

end MultiCorner
end CSTMicro
end Collatz2
