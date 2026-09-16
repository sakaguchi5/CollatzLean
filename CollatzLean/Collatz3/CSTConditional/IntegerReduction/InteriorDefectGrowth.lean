import CollatzLean.Collatz3.CSTConditional.IntegerReduction.RecordBoundaryDecomposition

/-!
# Collatz3 CSTConditional IntegerReduction: block 内 defect の下限

無限指数列自身の roof defect

`streamDefect(e,m) = beattyIndex(m) - prefixDepth(e,m)`

だけを薄い座標として追加する。

許容 block 分解があると、

* 全 prefix が global Beatty roof 以下、
* boundary では `streamDefect = boundaryDefect`、
* 一つの block 内では defect は開始 boundary defect を下回らない、
* 次 boundary に線形 defect bound があれば block 内 index にも
  `m ≤ K * (defect(m)+1)` が移る、

ことを derived theorem として得る。
-/

namespace Collatz3
namespace IntegerReduction

/-- 無限指数列の pure roof defect。 -/
def streamDefect
    (e : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  Critical.beattyIndex m - prefixDepth e m

/-- 許容分解の block boundary では pure defect と boundary defect が一致する。 -/
theorem streamDefect_boundaryIndex_eq_boundaryDefect
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n : ℕ) :
    streamDefect e (boundaryIndex r n) = boundaryDefect r n := by
  unfold streamDefect boundaryDefect
  rw [h.prefixDepth_boundaryIndex]

/--
許容 block 内の全 prefix は global Beatty roof 以下。
Nat.sub で defect を定義しても情報は失われない。
-/
theorem prefixDepth_le_beattyIndex_of_admissibleDecomposition
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n t : ℕ)
    (ht : t ≤ r n) :
    prefixDepth e (boundaryIndex r n + t) ≤
      Critical.beattyIndex (boundaryIndex r n + t) := by
  have hBoundary := boundaryDepth_le_beattyIndex_boundaryIndex r n
  have hLocal := h.blockPrefixTwoDepth_le_beattyIndex n t ht
  have hDepth := prefixDepth_add e (boundaryIndex r n) t
  have hAdd :=
    Critical.beattyIndex_add_lower (boundaryIndex r n) t
  rw [h.prefixDepth_boundaryIndex] at hDepth
  omega

/--
一つの許容 block 内では defect は開始 boundary defect を下回らない。
-/
theorem boundaryDefect_le_streamDefect_inside
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    (n t : ℕ)
    (ht : t ≤ r n) :
    boundaryDefect r n ≤
      streamDefect e (boundaryIndex r n + t) := by
  have hBoundary := boundaryDepth_le_beattyIndex_boundaryIndex r n
  have hLocal := h.blockPrefixTwoDepth_le_beattyIndex n t ht
  have hDepth := prefixDepth_add e (boundaryIndex r n) t
  have hAdd := Critical.beattyIndex_add_lower (boundaryIndex r n) t
  rw [h.prefixDepth_boundaryIndex] at hDepth
  unfold boundaryDefect streamDefect
  omega

/--
次 boundary で `F_(n+1) ≤ K δ_(n+1)` が成り立つなら、
block 内の任意位置 `m=F_n+t` で

`m ≤ K * (streamDefect(e,m)+1)`。

一 block で boundary defect が高々 `+1` しか増えないことだけを使う。
-/
theorem index_le_mul_streamDefect_add_one_inside
    {e r : ℕ → ℕ}
    (h : IsAdmissibleDecomposition e r)
    {K n t : ℕ}
    (ht : t ≤ r n)
    (hNextLinear :
      boundaryIndex r (n + 1) ≤ K * boundaryDefect r (n + 1)) :
    boundaryIndex r n + t ≤
      K * (streamDefect e (boundaryIndex r n + t) + 1) := by
  have hIndex :
      boundaryIndex r n + t ≤ boundaryIndex r (n + 1) := by
    rw [boundaryIndex_succ]
    omega
  have hDefectStep := boundaryDefect_succ_eq_or_succ r n
  have hFloor := boundaryDefect_le_streamDefect_inside h n t ht
  have hDefectNext :
      boundaryDefect r (n + 1) ≤
        streamDefect e (boundaryIndex r n + t) + 1 := by
    rcases hDefectStep with hFlat | hRise <;> omega
  exact
    le_trans hIndex
      (le_trans hNextLinear (Nat.mul_le_mul_left K hDefectNext))

end IntegerReduction
end Collatz3
