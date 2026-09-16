import CollatzLean.Collatz3.CSTConditional.IntegerReduction.RecordBoundaryDecomposition
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: right-record による境界の完全特徴付け

許容 block 分解の境界を、分解データそのものを参照せず exponent stream だけから
読み直す。

normalized scale

`rho_m = 2^(D_m) / 3^m`

自体は新しい実数定義にせず、比較

`rho_i > rho_j`

を exact な整数不等式

`2^(D_j) * 3^i < 2^(D_i) * 3^j`

として保存する。

中心結果は

`m が block boundary ↔ m は未来全体に対する strict right-record`

である。
-/

namespace Collatz3
namespace IntegerReduction

/--
位置 `i` の normalized coefficient scale が位置 `j` より strict に大きいことを、
分母を払った整数不等式で表す。
-/
def ScaleDominates
    (e : ℕ → ℕ)
    (i j : ℕ) : Prop :=
  2 ^ prefixDepth e j * 3 ^ i <
    2 ^ prefixDepth e i * 3 ^ j

/-- 位置 `m` が、それより未来の全位置を strict に scale 支配する。 -/
def IsRightScaleRecord
    (e : ℕ → ℕ)
    (m : ℕ) : Prop :=
  ∀ j : ℕ, m < j → ScaleDominates e m j

/-- scale 支配関係は推移的。 -/
theorem scaleDominates_trans
    {e : ℕ → ℕ}
    {i j k : ℕ}
    (hij : ScaleDominates e i j)
    (hjk : ScaleDominates e j k) :
    ScaleDominates e i k := by
  unfold ScaleDominates at hij hjk ⊢
  let A := 2 ^ prefixDepth e i
  let B := 2 ^ prefixDepth e j
  let C := 2 ^ prefixDepth e k
  let I := 3 ^ i
  let J := 3 ^ j
  let K := 3 ^ k
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have h₁ : (B * I) * C < (A * J) * C :=
    (Nat.mul_lt_mul_right hC).2 hij
  have h₂ : A * (C * J) < A * (B * K) :=
    (Nat.mul_lt_mul_left hA).2 hjk
  have hChain : B * (C * I) < B * (A * K) := by
    calc
      B * (C * I) = (B * I) * C := by ring
      _ < (A * J) * C := h₁
      _ = A * (C * J) := by ring
      _ < A * (B * K) := h₂
      _ = B * (A * K) := by ring
  have hB : 0 < B := by
    dsimp [B]
    positivity
  exact (Nat.mul_lt_mul_left hB).1 hChain

/-- 同じ位置を strict に scale 支配することはない。 -/
theorem not_scaleDominates_self
    (e : ℕ → ℕ)
    (m : ℕ) :
    ¬ ScaleDominates e m m := by
  unfold ScaleDominates
  exact lt_irrefl _

/-- scale 支配関係は反対向きと同時には成立しない。 -/
theorem scaleDominates_asymm
    {e : ℕ → ℕ}
    {i j : ℕ}
    (hij : ScaleDominates e i j)
    (hji : ScaleDominates e j i) :
    False := by
  exact (not_scaleDominates_self e i) (scaleDominates_trans hij hji)

namespace IsAdmissibleDecomposition

/-- 許容分解の boundary index は strict monotone。 -/
theorem boundaryIndex_strictMono
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r) :
    StrictMono (boundaryIndex r) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [boundaryIndex_succ]
  have hr := h.length_pos n
  omega

/-- 許容分解では `n ≤ F_n`。各 block length が正であることの累積版。 -/
theorem blockCount_le_boundaryIndex
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    n ≤ boundaryIndex r n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [boundaryIndex_succ]
      have hr := h.length_pos n
      omega

/--
任意の時刻 `m` はちょうど一つの half-open block
`[F_n,F_(n+1))` に入る。

ここでは存在だけを保存し、一意性は strict monotonicity から後で読む。
-/
theorem exists_blockLocation
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (m : ℕ) :
    ∃ n t : ℕ,
      t < r n ∧
      m = boundaryIndex r n + t := by
  have hExists :
      ∃ n : ℕ, m < boundaryIndex r (n + 1) := by
    refine ⟨m, ?_⟩
    have hBound := h.blockCount_le_boundaryIndex (m + 1)
    omega
  let n : ℕ := Nat.find hExists
  have hUpper : m < boundaryIndex r (n + 1) :=
    Nat.find_spec hExists
  have hLower : boundaryIndex r n ≤ m := by
    by_cases hn : n = 0
    · rw [hn]
      simp [boundaryIndex]
    · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
      have hPrevLt : n - 1 < n := by
        omega
      have hPrevNot := Nat.find_min hExists hPrevLt
      have hPrevIndex : (n - 1) + 1 = n := by
        omega
      rw [hPrevIndex] at hPrevNot
      omega
  let t : ℕ := m - boundaryIndex r n
  have hEq : m = boundaryIndex r n + t := by
    dsimp [t]
    omega
  have ht : t < r n := by
    rw [boundaryIndex_succ] at hUpper
    dsimp [t]
    omega
  exact ⟨n, t, ht, hEq⟩

/-- 一つの block の始点 boundary は、その block の終点 boundary を strict に支配する。 -/
theorem boundary_scaleDominates_succ
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    ScaleDominates e (boundaryIndex r n) (boundaryIndex r (n + 1)) := by
  have hMain :=
    h.blockStart_scale_dominates n (r n) (h.length_pos n) (le_rfl)
  unfold ScaleDominates
  rw [boundaryIndex_succ]
  exact hMain

/-- 前の boundary は、任意の後続 boundary を strict に支配する。 -/
theorem boundary_scaleDominates_laterBoundary
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    {n k : ℕ}
    (hnk : n < k) :
    ScaleDominates e (boundaryIndex r n) (boundaryIndex r k) := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      by_cases hnkEq : n = k
      · subst n
        exact h.boundary_scaleDominates_succ k
      · have hnlt : n < k := by omega
        exact scaleDominates_trans
          (ih hnlt)
          (h.boundary_scaleDominates_succ k)

/--
block の真の内部位置は、同じ block の終点 boundary より scale が strict に小さい。

これは許容 block の suffix 条件 B2 の global 版である。
-/
theorem blockEnd_scaleDominates_internal
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n t : ℕ)
    (htPos : 0 < t)
    (htLt : t < r n) :
    ScaleDominates e
      (boundaryIndex r (n + 1))
      (boundaryIndex r n + t) := by
  let F := boundaryIndex r n
  let q := r n - t
  have hqPos : 0 < q := by
    dsimp [q]
    omega
  have hqLt : q < r n := by
    dsimp [q]
    omega
  have hSum : t + q = r n := by
    dsimp [q]
    omega
  have hSplit := streamWord_add e F t q
  rw [hSum] at hSplit
  have hDrop :
      (streamWord e F (r n)).drop t =
        streamWord e (F + t) q := by
    rw [hSplit]
    simp [streamWord_length]
  have hSuffix :
      Critical.beattyIndex q + 1 ≤
        Word.twoSteps (streamWord e (F + t) q) := by
    have hqLt' :
        q < (streamWord e (boundaryIndex r n) (r n)).length := by
      simpa using hqLt
    have hRaw :=
      (h n).suffixTwoDepth_lower hqPos hqLt'
    unfold suffixTwoDepth at hRaw
    have hLen : (streamWord e F (r n)).length = r n := by
      simp
    rw [hLen] at hRaw
    have hSub : r n - q = t := by
      dsimp [q]
      omega
    rw [hSub, hDrop] at hRaw
    exact hRaw
  let H := Word.twoSteps (streamWord e (F + t) q)
  have hCritical :
      3 ^ q < 2 ^ (Critical.beattyIndex q + 1) := by
    simpa [Critical.criticalTwoDepth] using
      Critical.threePow_lt_twoPow_criticalTwoDepth q
  have hPowMono :
      2 ^ (Critical.beattyIndex q + 1) ≤ 2 ^ H := by
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    simpa [H] using hSuffix
  have hPow : 3 ^ q < 2 ^ H :=
    lt_of_lt_of_le hCritical hPowMono
  have hDepth :
      prefixDepth e (F + t + q) =
        prefixDepth e (F + t) + H := by
    dsimp [H]
    exact prefixDepth_add e (F + t) q
  have hEndIndex : F + t + q = boundaryIndex r (n + 1) := by
    rw [boundaryIndex_succ]
    dsimp [F]
    omega
  unfold ScaleDominates
  rw [← hEndIndex, hDepth]
  have hCommon :
      0 < 2 ^ prefixDepth e (F + t) * 3 ^ (F + t) := by
    positivity
  calc
    2 ^ prefixDepth e (F + t) * 3 ^ (F + t + q)
        = (2 ^ prefixDepth e (F + t) * 3 ^ (F + t)) * 3 ^ q := by
            rw [pow_add]
            ring
    _ < (2 ^ prefixDepth e (F + t) * 3 ^ (F + t)) * 2 ^ H :=
      (Nat.mul_lt_mul_left hCommon).2 hPow
    _ = 2 ^ (prefixDepth e (F + t) + H) * 3 ^ (F + t) := by
      rw [pow_add]
      ring

/--
任意の block boundary は未来全体に対する strict right-record。
-/
theorem boundary_isRightScaleRecord
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    IsRightScaleRecord e (boundaryIndex r n) := by
  intro j hj
  obtain ⟨k, t, ht, hjEq⟩ := h.exists_blockLocation j
  have hMono := h.boundaryIndex_strictMono
  have hnk : n ≤ k := by
    by_contra hNot
    have hklt : k < n := by omega
    have hkSuccLe : k + 1 ≤ n := by omega
    have hBoundaryLe :
        boundaryIndex r (k + 1) ≤ boundaryIndex r n :=
      hMono.monotone hkSuccLe
    have hjLt : j < boundaryIndex r (k + 1) := by
      rw [hjEq, boundaryIndex_succ]
      omega
    omega
  by_cases hEq : n = k
  · subst k
    have htPos : 0 < t := by
      rw [hjEq] at hj
      omega
    have hLocal := h.blockStart_scale_dominates n t htPos (Nat.le_of_lt ht)
    unfold ScaleDominates
    simpa [hjEq] using hLocal
  · have hnlt : n < k := by omega
    have hBoundary := h.boundary_scaleDominates_laterBoundary hnlt
    by_cases htZero : t = 0
    · subst t
      simpa [hjEq] using hBoundary
    · have htPos : 0 < t := Nat.pos_of_ne_zero htZero
      have hLocal :=
        h.blockStart_scale_dominates k t htPos (Nat.le_of_lt ht)
      have hLocal' :
          ScaleDominates e (boundaryIndex r k) j := by
        unfold ScaleDominates
        simpa [hjEq] using hLocal
      exact scaleDominates_trans hBoundary hLocal'

/--
right-record である時刻は必ず block boundary。

真の内部なら、後続する同じ block の終点 boundary の方が scale が大きくなり、
right-record 性に反する。
-/
theorem rightScaleRecord_is_boundary
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    {m : ℕ}
    (hRecord : IsRightScaleRecord e m) :
    ∃ n : ℕ, m = boundaryIndex r n := by
  obtain ⟨n, t, ht, hm⟩ := h.exists_blockLocation m
  by_cases htZero : t = 0
  · subst t
    exact ⟨n, by simpa using hm⟩
  · have htPos : 0 < t := Nat.pos_of_ne_zero htZero
    have hEndGt : m < boundaryIndex r (n + 1) := by
      rw [hm, boundaryIndex_succ]
      omega
    have hForward := hRecord (boundaryIndex r (n + 1)) hEndGt
    have hBackward := h.blockEnd_scaleDominates_internal n t htPos ht
    have hBackward' : ScaleDominates e (boundaryIndex r (n + 1)) m := by
      simpa [hm] using hBackward
    exact (scaleDominates_asymm hForward hBackward').elim

/--
許容分解における block boundary の内在的な完全特徴付け。

`m` が boundary であることと、`m` が未来全体に対する strict right-record であることは同値。
-/
theorem isRightScaleRecord_iff_exists_boundary
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (m : ℕ) :
    IsRightScaleRecord e m ↔
      ∃ n : ℕ, m = boundaryIndex r n := by
  constructor
  · exact h.rightScaleRecord_is_boundary
  · rintro ⟨n, rfl⟩
    exact h.boundary_isRightScaleRecord n

end IsAdmissibleDecomposition

end IntegerReduction
end Collatz3
