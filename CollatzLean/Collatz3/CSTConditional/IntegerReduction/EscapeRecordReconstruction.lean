import CollatzLean.Collatz3.CSTConditional.IntegerReduction.AdmissibleDecompositionUniqueness
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.EventualPeriodicity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: exponential escape から right-record 分解を再構成

Work 側で得た逆向き縮約を形式化する。

流れは三段階。

1. normalized coefficient scale

   `rho_m = 2^(D_m) / 3^m`

   が `0` に収束するなら、任意の tail は有限位置で一意な最大値を持つ。

2. right-record から次の tail maximum を順に取ると、隣接 record 間の exponent word は
   自動的に `IsAdmissibleBlock` になる。従って無限許容分解が再構成される。

3. 独立奇整数 recurrence が Problem E 型の指数下限

   `y_m ≥ 2^(m / L)`

   を十分先で満たすなら、`sum 1/(3*y_m)` は収束し、recurrence の補正積は一様有界。
   その結果 `rho_m → 0`。全体最大位置から shift すれば 0 が right-record となり、
   上の再構成を適用できる。

actual orbit / Global CST は使わない。
-/

namespace Collatz3
namespace IntegerReduction

open Filter
open scoped BigOperators Topology

/-- 計算可能な exact 有理数スケール。 -/
def coefficientScaleRat
    (e : ℕ → ℕ)
    (m : ℕ) : ℚ :=
  (2 : ℚ) ^ prefixDepth e m / (3 : ℚ) ^ m

/-- 解析用の実数スケール。 -/
noncomputable def coefficientScale
    (e : ℕ → ℕ)
    (m : ℕ) : ℝ :=
  (2 : ℝ) ^ prefixDepth e m / (3 : ℝ) ^ m

/-- coefficient scale は常に正。 -/
theorem coefficientScale_pos
    (e : ℕ → ℕ)
    (m : ℕ) :
    0 < coefficientScale e m := by
  unfold coefficientScale
  positivity

/-- 整数版 `ScaleDominates` と実数 scale 比較は exact に一致する。 -/
theorem scaleDominates_iff_coefficientScale_lt
    (e : ℕ → ℕ)
    (i j : ℕ) :
    ScaleDominates e i j ↔
      coefficientScale e j < coefficientScale e i := by
  unfold ScaleDominates coefficientScale
  have hi : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
  have hj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [div_lt_div_iff₀ hj hi]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- non-strict scale 比較の分母を払った形。 -/
theorem coefficientScale_le_iff_cross_le
    (e : ℕ → ℕ)
    (i j : ℕ) :
    coefficientScale e i ≤ coefficientScale e j ↔
      2 ^ prefixDepth e i * 3 ^ j ≤
        2 ^ prefixDepth e j * 3 ^ i := by
  unfold coefficientScale
  have hi : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
  have hj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [div_le_div_iff₀ hi hj]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/--
異なる index では coefficient scale は一致しない。

等値なら正の幅 `q` に対して `2^H = 3^q` が必要になるが、
`beattyIndex q` の strict power sandwich に反する。
-/
theorem coefficientScale_ne_of_lt
    (e : ℕ → ℕ)
    {i j : ℕ}
    (hij : i < j) :
    coefficientScale e i ≠ coefficientScale e j := by
  intro hEq
  let q : ℕ := j - i
  let H : ℕ := Word.twoSteps (streamWord e i q)
  have hqPos : 0 < q := by
    dsimp [q]
    omega
  have hIndex : i + q = j := by
    dsimp [q]
    omega
  have hDepth :
      prefixDepth e j = prefixDepth e i + H := by
    rw [← hIndex]
    dsimp [H]
    exact prefixDepth_add e i q
  have hCrossR :
      (2 : ℝ) ^ prefixDepth e i * (3 : ℝ) ^ j =
        (2 : ℝ) ^ prefixDepth e j * (3 : ℝ) ^ i := by
    have hi : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
    have hj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    unfold coefficientScale at hEq
    have h := (div_eq_div_iff (ne_of_gt hi) (ne_of_gt hj)).1 hEq
    simpa using h
  have hCrossN :
      2 ^ prefixDepth e i * 3 ^ j =
        2 ^ prefixDepth e j * 3 ^ i := by
    exact_mod_cast hCrossR
  rw [hDepth, ← hIndex, pow_add, pow_add] at hCrossN
  have hFactor :
      (2 ^ prefixDepth e i * 3 ^ i) * 3 ^ q =
        (2 ^ prefixDepth e i * 3 ^ i) * 2 ^ H := by
    calc
      (2 ^ prefixDepth e i * 3 ^ i) * 3 ^ q
          = 2 ^ prefixDepth e i * (3 ^ i * 3 ^ q) := by ring
      _ = (2 ^ prefixDepth e i * 2 ^ H) * 3 ^ i := hCrossN
      _ = (2 ^ prefixDepth e i * 3 ^ i) * 2 ^ H := by ring
  have hCommon : 0 < 2 ^ prefixDepth e i * 3 ^ i := by positivity
  have hPowEq : 3 ^ q = 2 ^ H :=
    Nat.mul_left_cancel hCommon hFactor
  have hBeatty := beattyIndex_power_characterization hqPos
  by_cases hH : H ≤ Critical.beattyIndex q
  · have hPowLe : 2 ^ H ≤ 2 ^ Critical.beattyIndex q :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hH
    omega
  · have hH' : Critical.beattyIndex q + 1 ≤ H := by omega
    have hPowLe :
        2 ^ (Critical.beattyIndex q + 1) ≤ 2 ^ H :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hH'
    omega

/-- 異なる index の coefficient scale は一致しない。 -/
theorem coefficientScale_ne_of_ne
    (e : ℕ → ℕ)
    {i j : ℕ}
    (hij : i ≠ j) :
    coefficientScale e i ≠ coefficientScale e j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact coefficientScale_ne_of_lt e h
  · exact Ne.symm (coefficientScale_ne_of_lt e h)

/-- tail `(F,∞)` 上で coefficient scale が最大となる位置。 -/
def IsTailScaleMaximum
    (e : ℕ → ℕ)
    (F G : ℕ) : Prop :=
  F < G ∧
    ∀ m : ℕ, F < m →
      coefficientScale e m ≤ coefficientScale e G

/--
`rho_m → 0` なら任意の tail は有限位置で最大値を持つ。
-/
theorem exists_tailScaleMaximum
    {e : ℕ → ℕ}
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (F : ℕ) :
    ∃ G : ℕ, IsTailScaleMaximum e F G := by
  let a : ℝ := coefficientScale e (F + 1)
  have ha : 0 < a := by
    dsimp [a]
    exact coefficientScale_pos e (F + 1)
  have hEventually :
      ∀ᶠ m : ℕ in atTop, coefficientScale e m < a :=
    (tendsto_order.1 hZero).2 a ha
  rw [eventually_atTop] at hEventually
  obtain ⟨N₀, hN₀⟩ := hEventually
  let N : ℕ := max N₀ (F + 1)
  let s : Finset ℕ := Finset.Icc (F + 1) N
  have hs : s.Nonempty := by
    refine ⟨F + 1, ?_⟩
    simp [s, N]
  obtain ⟨G, hGs, hGmax⟩ :=
    Finset.exists_max_image s (coefficientScale e) hs
  refine ⟨G, ?_, ?_⟩
  · have hmem := Finset.mem_Icc.mp hGs
    omega
  · intro m hFm
    by_cases hmN : m ≤ N
    · apply hGmax m
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    · have hN₀m : N₀ ≤ m := by
        dsimp [N] at hmN ⊢
        omega
      have hmSmall := hN₀ m hN₀m
      have hBaseLe : a ≤ coefficientScale e G := by
        apply hGmax (F + 1)
        simp [s, N]
      exact le_trans (le_of_lt hmSmall) hBaseLe

/-- tail maximum は一意。 -/
theorem tailScaleMaximum_unique
    {e : ℕ → ℕ}
    {F G H : ℕ}
    (hG : IsTailScaleMaximum e F G)
    (hH : IsTailScaleMaximum e F H) :
    G = H := by
  by_contra hNe
  have hGH := hG.2 H hH.1
  have hHG := hH.2 G hG.1
  have hEq : coefficientScale e G = coefficientScale e H :=
    le_antisymm hHG hGH
  exact (coefficientScale_ne_of_ne e hNe) hEq

/-- tail maximum は、その位置から見れば strict right-record。 -/
theorem tailScaleMaximum_isRightScaleRecord
    {e : ℕ → ℕ}
    {F G : ℕ}
    (hG : IsTailScaleMaximum e F G) :
    IsRightScaleRecord e G := by
  intro j hGj
  have hLe := hG.2 j (lt_trans hG.1 hGj)
  have hNe : coefficientScale e j ≠ coefficientScale e G := by
    exact Ne.symm (coefficientScale_ne_of_lt e hGj)
  have hLt : coefficientScale e j < coefficientScale e G :=
    lt_of_le_of_ne hLe hNe
  exact (scaleDominates_iff_coefficientScale_lt e G j).2 hLt

/--
前向き区間 `[F,F+r]` の scale decrease は、区間 depth の power inequality と同値。
-/
theorem scaleDominates_add_iff_twoPow_lt_threePow
    (e : ℕ → ℕ)
    (F r : ℕ) :
    ScaleDominates e F (F + r) ↔
      2 ^ Word.twoSteps (streamWord e F r) < 3 ^ r := by
  let H := Word.twoSteps (streamWord e F r)
  have hDepth : prefixDepth e (F + r) = prefixDepth e F + H := by
    dsimp [H]
    exact prefixDepth_add e F r
  have hCommon : 0 < 2 ^ prefixDepth e F * 3 ^ F := by positivity
  unfold ScaleDominates
  rw [hDepth, pow_add, pow_add]
  have hIff :
      (2 ^ prefixDepth e F * 3 ^ F) * 2 ^ H <
          (2 ^ prefixDepth e F * 3 ^ F) * 3 ^ r ↔
        2 ^ H < 3 ^ r :=
    Nat.mul_lt_mul_left hCommon
  simpa [H, mul_assoc, mul_left_comm, mul_comm] using hIff


/--
区間終点の scale が始点より大きいことは strict contracting power inequality と同値。
-/
theorem scaleDominates_add_reverse_iff_threePow_lt_twoPow
    (e : ℕ → ℕ)
    (F r : ℕ) :
    ScaleDominates e (F + r) F ↔
      3 ^ r < 2 ^ Word.twoSteps (streamWord e F r) := by
  let H := Word.twoSteps (streamWord e F r)
  have hDepth :
      prefixDepth e (F + r) =
        prefixDepth e F + H := by
    dsimp [H]
    exact prefixDepth_add e F r
  have hCommon :
      0 < 2 ^ prefixDepth e F * 3 ^ F := by
    positivity
  unfold ScaleDominates
  rw [hDepth, pow_add, pow_add]
  have hIff :
      (2 ^ prefixDepth e F * 3 ^ F) * 3 ^ r <
          (2 ^ prefixDepth e F * 3 ^ F) * 2 ^ H ↔
        3 ^ r < 2 ^ H :=
    Nat.mul_lt_mul_left hCommon
  simpa [H, mul_assoc, mul_left_comm, mul_comm] using hIff

/-- positive exponent stream の finite segment word は valid。 -/
theorem streamWord_valid_of_pos
    {e : ℕ → ℕ}
    (hPos : ∀ m : ℕ, 0 < e m)
    (F r : ℕ) :
    Word.Valid (streamWord e F r) := by
  induction r with
  | zero =>
      intro a ha
      simp at ha
  | succ r ih =>
      rw [streamWord_succ]
      exact (ih).append (by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl
        exact hPos (F + r))

/--
`F` が right-record、`G` が `(F,∞)` の tail maximum なら、
区間 `[F,G]` は許容ブロックになる。
-/
theorem admissibleBlock_between_record_and_tailMaximum
    {e : ℕ → ℕ}
    (hPos : ∀ m : ℕ, 0 < e m)
    {F G : ℕ}
    (hF : IsRightScaleRecord e F)
    (hG : IsTailScaleMaximum e F G) :
    IsAdmissibleBlock (streamWord e F (G - F)) := by
  let r : ℕ := G - F
  let w : Word := streamWord e F r
  let B : ℕ := Word.twoSteps w
  have hrPos : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hG.1
  have hFG : F + r = G := by
    dsimp [r]
    exact Nat.add_sub_of_le hG.1.le
  have hValid : Word.Valid w := by
    dsimp [w]
    exact streamWord_valid_of_pos hPos F r
  have hForward : ScaleDominates e F G := hF G hG.1
  have hPowLow : 2 ^ B < 3 ^ r := by
    have h :=
      (scaleDominates_add_iff_twoPow_lt_threePow e F r).1
        (by simpa [hFG] using hForward)
    simpa [B, w] using h
  have hNextLe : coefficientScale e (F + 1) ≤ coefficientScale e G :=
    hG.2 (F + 1) (by omega)
  have hCrossNext :
      2 ^ prefixDepth e (F + 1) * 3 ^ G ≤
        2 ^ prefixDepth e G * 3 ^ (F + 1) :=
    (coefficientScale_le_iff_cross_le e (F + 1) G).1 hNextLe
  have hDepthG : prefixDepth e G = prefixDepth e F + B := by
    rw [← hFG]
    dsimp [B, w]
    exact prefixDepth_add e F r
  have hDepthNext : prefixDepth e (F + 1) = prefixDepth e F + e F := by
    exact prefixDepth_succ e F
  have hCrossFactored :
      (2 ^ prefixDepth e F * 3 ^ F) *
          (2 ^ e F * 3 ^ r) ≤
        (2 ^ prefixDepth e F * 3 ^ F) *
          (2 ^ B * 3) := by
    have h := hCrossNext
    rw [hDepthNext, hDepthG, ← hFG] at h
    simp only [pow_add, pow_one] at h
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hCommon : 0 < 2 ^ prefixDepth e F * 3 ^ F := by positivity
  have hRatioLower : 2 ^ e F * 3 ^ r ≤ 2 ^ B * 3 :=
    Nat.le_of_mul_le_mul_left hCrossFactored hCommon
  have hTwoLe : 2 ≤ 2 ^ e F := by
    have he := hPos F
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ e F by omega)
    norm_num at this ⊢
    exact this
  have hThreeHalf : 2 * 3 ^ r ≤ 3 * 2 ^ B := by
    calc
      2 * 3 ^ r ≤ 2 ^ e F * 3 ^ r :=
        Nat.mul_le_mul_right (3 ^ r) hTwoLe
      _ ≤ 2 ^ B * 3 := hRatioLower
      _ = 3 * 2 ^ B := by ring
  have hPowHigh : 3 ^ r < 2 ^ (B + 1) := by
    have hBPos : 0 < 2 ^ B := by positivity
    have hAux : 3 ^ r < 2 * 2 ^ B := by
      nlinarith
    simpa [pow_succ, Nat.mul_comm] using hAux
  have hBeattyLow : B ≤ Critical.beattyIndex r :=
    Critical.le_beattyIndex_of_twoPow_lt_threePow hPowLow
  have hBeattyHigh : Critical.beattyIndex r ≤ B := by
    exact Critical.beattyIndex_le_of_upper (Nat.le_of_lt hPowHigh)
  have hTotal : B = Critical.beattyIndex r := by omega
  refine ⟨?_, hValid, ?_, ?_⟩
  · simpa [w, r] using hrPos
  · simpa [B, w, r] using hTotal
  · intro q hqPos hqLt
    have hqLtR : q < r := by
      simpa [w, r] using hqLt
    let t : ℕ := r - q
    have htPos : 0 < t := by
      dsimp [t]
      omega
    have htLt : t < r := by
      dsimp [t]
      omega
    have hTIndex : F + t < G := by
      rw [← hFG]
      omega
    have hInternalLe := hG.2 (F + t) (by omega)
    have hInternalNe :
        coefficientScale e (F + t) ≠ coefficientScale e G := by
      exact coefficientScale_ne_of_lt e hTIndex
    have hInternalLt :
        coefficientScale e (F + t) < coefficientScale e G :=
      lt_of_le_of_ne hInternalLe hInternalNe
    have hContract : ScaleDominates e G (F + t) :=
      (scaleDominates_iff_coefficientScale_lt e G (F + t)).2 hInternalLt
    have hTQ : F + t + q = G := by
      rw [← hFG]
      dsimp [t]
      omega
    have hSuffixPow :
        3 ^ q < 2 ^ Word.twoSteps (streamWord e (F + t) q) := by
      have hRev :=
        (scaleDominates_add_reverse_iff_threePow_lt_twoPow e (F + t) q).1
          (by simpa [hTQ] using hContract)
      exact hRev
    have hSuffixLower :
        Critical.beattyIndex q + 1 ≤
          Word.twoSteps (streamWord e (F + t) q) := by
      by_contra hNot
      have hLe :
          Word.twoSteps (streamWord e (F + t) q) ≤
            Critical.beattyIndex q := by omega
      have hPowLe :
          2 ^ Word.twoSteps (streamWord e (F + t) q) ≤
            2 ^ Critical.beattyIndex q :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hLe
      have hBeat := Critical.beattyIndex_lower_strict hqPos
      omega
    have hSplit := streamWord_add e F t q
    have hSum : t + q = r := by
      dsimp [t]
      omega
    rw [hSum] at hSplit
    have hDrop : w.drop t = streamWord e (F + t) q := by
      dsimp [w]
      rw [hSplit]
      simp [streamWord_length]
    unfold suffixTwoDepth
    have hLen : w.length = r := by
      dsimp [w]
      simp
    rw [hLen]
    have hSub : r - q = t := by
      dsimp [t]
    rw [hSub, hDrop]
    exact hSuffixLower

/--
`rho→0` の下で right-record から次の tail maximum を再帰的に選ぶ boundary 列。
-/
noncomputable def reconstructedBoundary
    (e : ℕ → ℕ)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0)) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      Classical.choose
        (exists_tailScaleMaximum hZero (reconstructedBoundary e hZero n))

/-- 再構成 boundary の隣接差。 -/
noncomputable def reconstructedLength
    (e : ℕ → ℕ)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (n : ℕ) : ℕ :=
  reconstructedBoundary e hZero (n + 1) -
    reconstructedBoundary e hZero n

/-- 再構成の次 boundary は現在 boundary より先の tail maximum。 -/
theorem reconstructedBoundary_succ_spec
    (e : ℕ → ℕ)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (n : ℕ) :
    IsTailScaleMaximum e
      (reconstructedBoundary e hZero n)
      (reconstructedBoundary e hZero (n + 1)) := by
  change IsTailScaleMaximum e
    (reconstructedBoundary e hZero n)
    (Classical.choose
      (exists_tailScaleMaximum hZero (reconstructedBoundary e hZero n)))
  exact Classical.choose_spec
    (exists_tailScaleMaximum hZero (reconstructedBoundary e hZero n))

/-- 再構成 boundary は strict monotone。 -/
theorem reconstructedBoundary_strictMono
    (e : ℕ → ℕ)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0)) :
    StrictMono (reconstructedBoundary e hZero) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (reconstructedBoundary_succ_spec e hZero n).1

/-- reconstructed length は正。 -/
theorem reconstructedLength_pos
    (e : ℕ → ℕ)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (n : ℕ) :
    0 < reconstructedLength e hZero n := by
  unfold reconstructedLength
  exact Nat.sub_pos_of_lt ((reconstructedBoundary_succ_spec e hZero n).1)

/-- reconstructed length の累積 boundary は再構成 boundary 自身。 -/
theorem boundaryIndex_reconstructedLength
    (e : ℕ → ℕ)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0)) :
    ∀ n : ℕ,
      boundaryIndex (reconstructedLength e hZero) n =
        reconstructedBoundary e hZero n := by
  intro n
  induction n with
  | zero =>
      simp [boundaryIndex, reconstructedBoundary]
  | succ n ih =>
      rw [boundaryIndex_succ, ih]
      unfold reconstructedLength
      have hLt := (reconstructedBoundary_succ_spec e hZero n).1
      omega

/--
0 自身が right-record なら、再構成された全 boundary も right-record。
-/
theorem reconstructedBoundary_isRightScaleRecord
    {e : ℕ → ℕ}
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (hZeroRecord : IsRightScaleRecord e 0) :
    ∀ n : ℕ,
      IsRightScaleRecord e (reconstructedBoundary e hZero n) := by
  intro n
  cases n with
  | zero =>
      simpa [reconstructedBoundary] using hZeroRecord
  | succ n =>
      exact
        tailScaleMaximum_isRightScaleRecord
          (reconstructedBoundary_succ_spec e hZero n)

/--
`rho→0` かつ 0 が right-record なら、right-record の連鎖から許容 block 分解を再構成できる。
-/
theorem reconstructed_isAdmissibleDecomposition
    {e : ℕ → ℕ}
    (hPos : ∀ m : ℕ, 0 < e m)
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (hZeroRecord : IsRightScaleRecord e 0) :
    IsAdmissibleDecomposition e (reconstructedLength e hZero) := by
  intro n
  have hBoundary := boundaryIndex_reconstructedLength e hZero n
  have hRecord := reconstructedBoundary_isRightScaleRecord hZero hZeroRecord n
  have hMax := reconstructedBoundary_succ_spec e hZero n
  have hBlock := admissibleBlock_between_record_and_tailMaximum hPos hRecord hMax
  have hLenEq :
      reconstructedLength e hZero n =
        reconstructedBoundary e hZero (n + 1) -
          reconstructedBoundary e hZero n := rfl
  rw [hBoundary]
  simpa [hLenEq] using hBlock

/-! ## Problem E から coefficient scale の減衰へ -/

/--
Work の縮約問題 E に現れる指数的下限。

ある固定 `L>0` と十分遅い時刻 `M` が存在し、全 `m≥M` で
`2^(m/L) ≤ y_m`。
-/
def HasExponentialEscape
    (y : ℕ → ℕ) : Prop :=
  ∃ L M : ℕ,
    0 < L ∧
      ∀ m : ℕ, M ≤ m → 2 ^ (m / L) ≤ y m

/-- `m ↦ (1/2)^(m/L)` は `L>0` なら summable。 -/
theorem summable_half_pow_natDiv
    {L : ℕ}
    (hL : 0 < L) :
    Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m / L)) := by
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hGeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_two
  have hFin : Summable (fun _ : Fin L => (1 : ℝ)) :=
    Summable.of_finite
  have hProd :
      Summable (fun p : ℕ × Fin L => (1 / 2 : ℝ) ^ p.1) := by
    have hMul :=
      hGeom.mul_of_nonneg hFin
        (fun _ => by positivity)
        (fun _ => by positivity)
    simpa using hMul
  have hPull :
      Summable
        ((fun p : ℕ × Fin L => (1 / 2 : ℝ) ^ p.1) ∘ Nat.divModEquiv L) :=
    (Nat.divModEquiv L).summable_iff.mpr hProd
  simpa [Function.comp_def, Nat.divModEquiv] using hPull

/-- Problem E の指数下限だけから reciprocal correction 級数の収束が従う。 -/
theorem summable_reciprocal_of_exponentialEscape
    {y : ℕ → ℕ}
    (hEscape : HasExponentialEscape y) :
    Summable (fun m : ℕ => 1 / (3 * (y m : ℝ))) := by
  obtain ⟨L, M, hL, hMain⟩ := hEscape
  have hHalf := summable_half_pow_natDiv hL
  have hMajor :
      Summable (fun n : ℕ =>
        1 / (3 * (2 : ℝ) ^ (n / L))) := by
    have h := hHalf.mul_left (1 / 3 : ℝ)
    refine h.congr ?_
    intro n
    field_simp
    ring_nf
    simp
  have hTail :
      Summable (fun n : ℕ =>
        1 / (3 * (y (n + M) : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have hDiv : n / L ≤ (n + M) / L :=
        Nat.div_le_div_right (Nat.le_add_right n M)
      have hPow : 2 ^ (n / L) ≤ 2 ^ ((n + M) / L) :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDiv
      have hY := hMain (n + M) (by omega)
      have hDenNat : 3 * 2 ^ (n / L) ≤ 3 * y (n + M) := by
        exact Nat.mul_le_mul_left 3 (le_trans hPow hY)
      have hDenReal :
          (3 : ℝ) * (2 : ℝ) ^ (n / L) ≤
            (3 : ℝ) * (y (n + M) : ℝ) := by
        exact_mod_cast hDenNat
      have hPosLeft : 0 < (3 : ℝ) * (2 : ℝ) ^ (n / L) := by positivity
      exact one_div_le_one_div_of_le hPosLeft hDenReal
    · simpa [Nat.add_comm] using hMajor
  exact (summable_nat_add_iff M).1 (by simpa [Nat.add_comm] using hTail)

/-- recurrence の一段 correction factor の exact 有理数版。 -/
def recurrenceCorrectionRat
    (y : ℕ → ℕ)
    (m : ℕ) : ℚ :=
  1 + 1 / (3 * (y m : ℚ))

/-- 先頭 `m` correction factors の exact 有理数有限積。 -/
def recurrenceCorrectionProductRat
    (y : ℕ → ℕ)
    (m : ℕ) : ℚ :=
  ∏ i ∈ Finset.range m, recurrenceCorrectionRat y i

/-- recurrence の一段 correction factor の実数版。 -/
noncomputable def recurrenceCorrection
    (y : ℕ → ℕ)
    (m : ℕ) : ℝ :=
  (recurrenceCorrectionRat y m : ℝ)

/-- 先頭 `m` correction factors の実数有限積。 -/
noncomputable def recurrenceCorrectionProduct
    (y : ℕ → ℕ)
    (m : ℕ) : ℝ :=
  (recurrenceCorrectionProductRat y m : ℝ)

@[simp] theorem recurrenceCorrection_eq_real
    (y : ℕ → ℕ)
    (m : ℕ) :
    recurrenceCorrection y m =
      1 + 1 / (3 * (y m : ℝ)) := by
  simp [recurrenceCorrection, recurrenceCorrectionRat]

@[simp] theorem recurrenceCorrectionProduct_eq_real_prod
    (y : ℕ → ℕ)
    (m : ℕ) :
    recurrenceCorrectionProduct y m =
      ∏ i ∈ Finset.range m,
        (1 + 1 / (3 * (y i : ℝ))) := by
  simp [recurrenceCorrectionProduct,
    recurrenceCorrectionProductRat,
    recurrenceCorrectionRat]

/--
奇整数 recurrence の exact product identity。

`rho_m * y_m = y_0 * Π_{j<m}(1 + 1/(3y_j))`。
-/
theorem coefficientScale_mul_value_eq_correctionProduct
    {e y : ℕ → ℕ}
    (hRun : RunsOddRecurrence e y) :
    ∀ m : ℕ,
      coefficientScale e m * (y m : ℝ) =
        (y 0 : ℝ) * recurrenceCorrectionProduct y m := by
  intro m
  induction m with
  | zero =>
      simp [coefficientScale, recurrenceCorrectionProduct,
        recurrenceCorrectionProductRat, prefixDepth, prefixWord]
  | succ m ih =>
      have hStepNat := hRun.equation m
      have hStep :
          (2 : ℝ) ^ e m * (y (m + 1) : ℝ) =
            3 * (y m : ℝ) + 1 := by
        exact_mod_cast hStepNat
      have hyPos : 0 < (y m : ℝ) := by
        rcases hRun.value_odd m with ⟨q, hq⟩
        have : 0 < y m := by omega
        exact_mod_cast this
      have hScaleStep :
          coefficientScale e (m + 1) * (y (m + 1) : ℝ) =
            coefficientScale e m * (y m : ℝ) * recurrenceCorrection y m := by
        calc
          coefficientScale e (m + 1) * (y (m + 1) : ℝ)
              = coefficientScale e m *
                  (((2 : ℝ) ^ e m * (y (m + 1) : ℝ)) / 3) := by
                    simp [coefficientScale, prefixDepth_succ, pow_add, pow_succ]
                    ring
          _ = coefficientScale e m *
                ((3 * (y m : ℝ) + 1) / 3) := by rw [hStep]
          _ = coefficientScale e m * (y m : ℝ) * recurrenceCorrection y m := by
            rw [recurrenceCorrection_eq_real]
            field_simp [ne_of_gt hyPos]
      rw [hScaleStep, ih]
      simp only [recurrenceCorrectionProduct_eq_real_prod,
        Finset.prod_range_succ,
        recurrenceCorrection_eq_real]
      ring

/-- correction product は reciprocal series の exponential で一様に上から抑えられる。 -/
theorem correctionProduct_le_exp_tsum
    {y : ℕ → ℕ}
    (hSum : Summable (fun m : ℕ => 1 / (3 * (y m : ℝ))))
    (m : ℕ) :
    recurrenceCorrectionProduct y m ≤
      Real.exp (∑' i : ℕ, 1 / (3 * (y i : ℝ))) := by
  let u : ℕ → ℝ := fun i => 1 / (3 * (y i : ℝ))
  have huNonneg : ∀ i : ℕ, 0 ≤ u i := by
    intro i
    positivity
  have hProd :
      recurrenceCorrectionProduct y m ≤
        Real.exp (∑ i ∈ Finset.range m, u i) := by
    rw [recurrenceCorrectionProduct_eq_real_prod]
    simpa [u] using
      Real.prod_one_add_le_exp_sum (Finset.range m) huNonneg
  have hSumLe :
      (∑ i ∈ Finset.range m, u i) ≤ ∑' i, u i := by
    exact hSum.sum_le_tsum (Finset.range m) (fun i _ => huNonneg i)
  exact le_trans hProd (Real.exp_le_exp.mpr hSumLe)

/-- Problem E の下では `1 / y_m → 0`。 -/
theorem reciprocal_value_tendsto_zero_of_exponentialEscape
    {y : ℕ → ℕ}
    (hOdd : ∀ m : ℕ, Odd (y m))
    (hEscape : HasExponentialEscape y) :
    Tendsto (fun m : ℕ => 1 / (y m : ℝ)) atTop (𝓝 0) := by
  have hSum := summable_reciprocal_of_exponentialEscape hEscape
  have hScaled :
      Summable (fun m : ℕ => 1 / (y m : ℝ)) := by
    have h := hSum.mul_left (3 : ℝ)
    refine h.congr ?_
    intro m
    have hyNeNat : y m ≠ 0 := by
      rcases hOdd m with ⟨q, hq⟩
      omega
    have hyNe : (y m : ℝ) ≠ 0 := by
      exact_mod_cast hyNeNat
    field_simp [hyNe]
  exact hScaled.tendsto_atTop_zero

/--
Problem E を満たす奇整数 recurrence では coefficient scale が `0` に収束する。
-/
theorem coefficientScale_tendsto_zero_of_exponentialEscape
    {e y : ℕ → ℕ}
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    Tendsto (coefficientScale e) atTop (𝓝 0) := by
  have hOdd := hRun.value_odd
  have hSum := summable_reciprocal_of_exponentialEscape hEscape
  let C : ℝ :=
    (y 0 : ℝ) * Real.exp (∑' i : ℕ, 1 / (3 * (y i : ℝ)))
  have hInv := reciprocal_value_tendsto_zero_of_exponentialEscape hOdd hEscape
  have hUpper :
      ∀ m : ℕ,
        coefficientScale e m ≤ C * (1 / (y m : ℝ)) := by
    intro m
    have hIdentity := coefficientScale_mul_value_eq_correctionProduct hRun m
    have hProd := correctionProduct_le_exp_tsum hSum m
    have hyPos : 0 < (y m : ℝ) := by
      rcases hOdd m with ⟨q, hq⟩
      have : 0 < y m := by omega
      exact_mod_cast this
    have hScaleEq :
        coefficientScale e m =
          ((y 0 : ℝ) * recurrenceCorrectionProduct y m) / (y m : ℝ) := by
      apply (eq_div_iff (ne_of_gt hyPos)).2
      nlinarith [hIdentity]
    rw [hScaleEq]
    dsimp [C]
    have hNum :
        (y 0 : ℝ) * recurrenceCorrectionProduct y m ≤
          (y 0 : ℝ) * Real.exp (∑' i : ℕ, 1 / (3 * (y i : ℝ))) := by
      gcongr
    have hInvNonneg : 0 ≤ 1 / (y m : ℝ) := by positivity
    calc
      ((y 0 : ℝ) * recurrenceCorrectionProduct y m) / (y m : ℝ)
          = ((y 0 : ℝ) * recurrenceCorrectionProduct y m) *
              (1 / (y m : ℝ)) := by ring
      _ ≤ ((y 0 : ℝ) * Real.exp (∑' i : ℕ, 1 / (3 * (y i : ℝ)))) *
              (1 / (y m : ℝ)) :=
            mul_le_mul_of_nonneg_right hNum hInvNonneg
  have hLower : ∀ m : ℕ, (0 : ℝ) ≤ coefficientScale e m := by
    intro m
    exact le_of_lt (coefficientScale_pos e m)
  have hTarget :
      Tendsto (fun m : ℕ => C * (1 / (y m : ℝ))) atTop (𝓝 0) := by
    simpa using hInv.const_mul C
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper)
    hTarget

/-- `rho→0` なら全体最大位置が存在する。 -/
theorem exists_globalScaleMaximum
    {e : ℕ → ℕ}
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0)) :
    ∃ h : ℕ,
      ∀ m : ℕ,
        coefficientScale e m ≤ coefficientScale e h := by
  let a : ℝ := coefficientScale e 0
  have ha : 0 < a := coefficientScale_pos e 0
  have hEventually :
      ∀ᶠ m : ℕ in atTop, coefficientScale e m < a :=
    (tendsto_order.1 hZero).2 a ha
  rw [eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  let s : Finset ℕ := Finset.range (N + 1)
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  obtain ⟨h, hhMem, hhMax⟩ :=
    Finset.exists_max_image s (coefficientScale e) hs
  refine ⟨h, ?_⟩
  intro m
  by_cases hm : m ≤ N
  · apply hhMax m
    simp [s, hm]
  · have hmN : N ≤ m := by omega
    have hmSmall := hN m hmN
    have hZeroLe : a ≤ coefficientScale e h := by
      apply hhMax 0
      simp [s]
    exact le_trans (le_of_lt hmSmall) hZeroLe

/-- global maximum は異なる全位置より strict に大きい。 -/
theorem globalScaleMaximum_strict
    {e : ℕ → ℕ}
    {h : ℕ}
    (hMax : ∀ m : ℕ, coefficientScale e m ≤ coefficientScale e h)
    {m : ℕ}
    (hm : m ≠ h) :
    coefficientScale e m < coefficientScale e h := by
  exact lt_of_le_of_ne (hMax m) (coefficientScale_ne_of_ne e hm)

/-- shift 後の prefix depth 加法。 -/
theorem prefixDepth_shiftSeq
    (e : ℕ → ℕ)
    (h m : ℕ) :
    prefixDepth e (h + m) =
      prefixDepth e h + prefixDepth (shiftSeq e h) m := by
  induction m with
  | zero =>
      simp [prefixDepth, prefixWord]
  | succ m ih =>
      rw [show h + (m + 1) = (h + m) + 1 by omega]
      rw [prefixDepth_succ, prefixDepth_succ, ih]
      simp [shiftSeq, Nat.add_assoc]

/-- shift 後 scale は元 scale の比。 -/
theorem coefficientScale_shiftSeq
    (e : ℕ → ℕ)
    (h m : ℕ) :
    coefficientScale (shiftSeq e h) m =
      coefficientScale e (h + m) / coefficientScale e h := by
  unfold coefficientScale
  rw [prefixDepth_shiftSeq, pow_add, pow_add]
  field_simp

/-- `rho→0` は finite shift 後にも保存される。 -/
theorem coefficientScale_shift_tendsto_zero
    {e : ℕ → ℕ}
    (hZero : Tendsto (coefficientScale e) atTop (𝓝 0))
    (h : ℕ) :
    Tendsto (coefficientScale (shiftSeq e h)) atTop (𝓝 0) := by
  have hIndex : Tendsto (fun m : ℕ => h + m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hTail := hZero.comp hIndex
  have hDiv := hTail.div_const (coefficientScale e h)
  have hEq :
      coefficientScale (shiftSeq e h) =
        (fun m : ℕ => coefficientScale e (h + m) / coefficientScale e h) := by
    funext m
    exact coefficientScale_shiftSeq e h m
  rw [hEq]
  simpa [Function.comp_def] using hDiv

/-- global maximum から shift すると 0 は right-record。 -/
theorem zero_isRightScaleRecord_of_globalMaximum
    {e : ℕ → ℕ}
    {h : ℕ}
    (hMax : ∀ m : ℕ, coefficientScale e m ≤ coefficientScale e h) :
    IsRightScaleRecord (shiftSeq e h) 0 := by
  intro j hj
  have hStrict :
      coefficientScale e (h + j) < coefficientScale e h := by
    apply globalScaleMaximum_strict hMax
    omega
  have hShiftScale :
      coefficientScale (shiftSeq e h) j <
        coefficientScale (shiftSeq e h) 0 := by
    rw [coefficientScale_shiftSeq, coefficientScale_shiftSeq]
    simp only [Nat.add_zero]
    have hPos : 0 < coefficientScale e h := coefficientScale_pos e h
    apply (div_lt_div_iff₀ hPos hPos).2
    nlinarith
  exact (scaleDominates_iff_coefficientScale_lt (shiftSeq e h) 0 j).2 hShiftScale

/--
Problem E 型指数逃走を満たす独立奇整数 recurrence から、有限 shift 後に無限許容分解が存在する。
-/
theorem exists_shift_admissibleDecomposition_of_exponentialEscape
    {e y : ℕ → ℕ}
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    ∃ h : ℕ, ∃ r : ℕ → ℕ,
      IsAdmissibleDecomposition (shiftSeq e h) r := by
  have hZero := coefficientScale_tendsto_zero_of_exponentialEscape hRun hEscape
  obtain ⟨h, hMax⟩ := exists_globalScaleMaximum hZero
  have hShiftZero := coefficientScale_shift_tendsto_zero hZero h
  have hZeroRecord := zero_isRightScaleRecord_of_globalMaximum hMax
  have hShiftRun := hRun.shift h
  refine ⟨h, reconstructedLength (shiftSeq e h) hShiftZero, ?_⟩
  exact reconstructed_isAdmissibleDecomposition
    hShiftRun.exponent_pos hShiftZero hZeroRecord

end IntegerReduction
end Collatz3
