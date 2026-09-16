import CollatzLean.Collatz3.CSTConditional.IntegerReduction.CanonicalResidueBlock
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.BlockDefect
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: 許容 block 分解と scale record

無限指数列 `e` と block length 列 `r` の対応を、

`streamWord e (boundaryIndex r n) (r n)`

が各 `n` で許容ブロックである、という一つの薄い predicate だけで保存する。

そこから

* block 長は正、
* block boundary の prefix depth は `boundaryDepth` と一致、
* 各 block 内では開始 boundary の normalized coefficient scale が strict に最大、

をすべて derived theorem として得る。

normalized scale 自体を実数商として定義せず、比較は

`2^D_j * 3^i < 2^D_i * 3^j`

という純整数不等式で保存する。
-/

namespace Collatz3
namespace IntegerReduction

/-- 無限指数列を許容 block length 列 `r` で分解できること。 -/
def IsAdmissibleDecomposition
    (e r : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    IsAdmissibleBlock
      (streamWord e (boundaryIndex r n) (r n))

namespace IsAdmissibleDecomposition

/-- 各 block length は正。 -/
theorem length_pos
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    0 < r n := by
  have hn := (h n).length_pos
  simpa using hn

/-- 各 block の total depth はその長さの Beatty index。 -/
theorem blockTwoSteps_eq_beattyIndex
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    Word.twoSteps
        (streamWord e (boundaryIndex r n) (r n)) =
      Critical.beattyIndex (r n) := by
  simpa [streamWord] using
    (h n).totalTwoDepth_eq_beattyIndex

/-- 各 block の長さは `IsAdmissibleLength`。 -/
theorem isAdmissibleLength
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    IsAdmissibleLength (r n) := by
  simpa [streamWord] using
    (h n).isAdmissibleLength

/--
block boundary の global prefix depth は、block length だけから作った
`boundaryDepth` と exact に一致する。
-/
theorem prefixDepth_boundaryIndex
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    prefixDepth e (boundaryIndex r n) = boundaryDepth r n := by
  induction n with
  | zero =>
      simp [prefixDepth, boundaryIndex, boundaryDepth]
  | succ n ih =>
      rw [boundaryIndex_succ, prefixDepth_add, ih, boundaryDepth_succ]
      rw [h.blockTwoSteps_eq_beattyIndex n]

/--
一つの許容 block の任意 prefix は local Beatty roof 以下。
終端 `t=r_n` も含む形。
-/
theorem blockPrefixTwoDepth_le_beattyIndex
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n t : ℕ)
    (ht : t ≤ r n) :
    Word.twoSteps
        (streamWord e (boundaryIndex r n) t) ≤
      Critical.beattyIndex t := by
  by_cases ht0 : t = 0
  · subst t
    simp
  by_cases htFull : t = r n
  · subst t
    rw [h.blockTwoSteps_eq_beattyIndex n]
  · have htLt : t < r n := by
      omega
    have htLt' :
        t < (streamWord e (boundaryIndex r n) (r n)).length := by
      simpa [streamWord] using htLt
    have hPrefix :=
      (h n).prefixTwoDepth_le_beattyIndex
        (t := t) (Nat.pos_of_ne_zero ht0) htLt'
    rw [prefixTwoDepth_streamWord e (boundaryIndex r n) (r n) t ht] at hPrefix
    exact hPrefix

/--
block 内の任意の正の位置では、開始 boundary の scale が strict に大きい。

`rho_m = 2^D_m / 3^m` と書くなら `rho_start > rho_(start+t)` だが、
定理自体は商を使わない。
-/
theorem blockStart_scale_dominates
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n t : ℕ)
    (htPos : 0 < t)
    (ht : t ≤ r n) :
    2 ^ prefixDepth e (boundaryIndex r n + t) *
        3 ^ boundaryIndex r n <
      2 ^ prefixDepth e (boundaryIndex r n) *
        3 ^ (boundaryIndex r n + t) := by
  let F := boundaryIndex r n
  let H := Word.twoSteps (streamWord e F t)
  have hDepth : prefixDepth e (F + t) = prefixDepth e F + H := by
    dsimp [F, H]
    exact prefixDepth_add e (boundaryIndex r n) t
  have hRoof : H ≤ Critical.beattyIndex t := by
    dsimp [H, F]
    exact h.blockPrefixTwoDepth_le_beattyIndex n t ht
  have hPowLe : 2 ^ H ≤ 2 ^ Critical.beattyIndex t :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hRoof
  have hPow : 2 ^ H < 3 ^ t :=
    lt_of_le_of_lt hPowLe (Critical.beattyIndex_lower_strict htPos)
  have hCommon : 0 < 2 ^ prefixDepth e F * 3 ^ F := by positivity
  calc
    2 ^ prefixDepth e (F + t) * 3 ^ F
        = (2 ^ prefixDepth e F * 3 ^ F) * 2 ^ H := by
            rw [hDepth, pow_add]
            ring
    _ < (2 ^ prefixDepth e F * 3 ^ F) * 3 ^ t :=
      (Nat.mul_lt_mul_left hCommon).2 hPow
    _ = 2 ^ prefixDepth e F * 3 ^ (F + t) := by
      rw [pow_add]
      ring

end IsAdmissibleDecomposition

end IntegerReduction
end Collatz3
