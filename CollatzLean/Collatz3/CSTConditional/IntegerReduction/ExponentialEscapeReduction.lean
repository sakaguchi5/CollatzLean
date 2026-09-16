import CollatzLean.Collatz3.CSTConditional.IntegerReduction.OddRecurrence

/-!
# Collatz3 CSTConditional IntegerReduction: defect から指数的 escape へ

Work 側の「問題 E」へ向かううち、完全に有限・整数的に閉じる向きだけを保存する。

許容 block 分解 + 奇整数 recurrence があると、block 内でも prefix depth は Beatty roof 以下。
そのため

`2^(streamDefect(e,m)) < y_m`

が exact に従う。

さらに boundary の linear defect lower bound と合わせると、block 内 index について

`m ≤ K * (streamDefect(e,m)+1)`

も同時に得られる。

ここでは未解決の逆向き存在命題を definition や axiom にしない。
-/

namespace Collatz3
namespace IntegerReduction

/--
許容分解上の任意 block 内位置では、defect の 2 冪が recurrence value より strict に小さい。
-/
theorem twoPow_streamDefect_lt_value_inside
    {e y r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (hRun : RunsOddRecurrence e y)
    (n t : ℕ)
    (ht : t ≤ r n)
    (hIndexPos : 0 < boundaryIndex r n + t) :
    2 ^ streamDefect e (boundaryIndex r n + t) <
      y (boundaryIndex r n + t) := by
  let m := boundaryIndex r n + t
  have hRoof :=
    prefixDepth_le_beattyIndex_of_admissibleDecomposition hDec n t ht
  have hDefectEq :
      Critical.beattyIndex m =
        prefixDepth e m + streamDefect e m := by
    dsimp [m]
    unfold streamDefect
    omega
  have hBeatty := Critical.beattyIndex_lower_strict hIndexPos
  have hPrefixEq := hRun.prefixEquation m
  have hy0Pos : 0 < y 0 := by
    rcases hRun.value_odd 0 with ⟨q, hq⟩
    omega
  have hmPos : 0 < m := by
    simpa [m] using hIndexPos
  have hNumerator :
      3 ^ m < 2 ^ prefixDepth e m * y m := by
    calc
      3 ^ m ≤ 3 ^ m * y 0 := by
        simpa using
          Nat.mul_le_mul_left (3 ^ m) (show 1 ≤ y 0 by omega)
      _ < 3 ^ m * y 0 + prefixAffine e m := by
        have hAffinePos : 0 < prefixAffine e m := by
          obtain ⟨k, hk⟩ :=
            Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmPos)
          rw [hk, prefixAffine_succ]
          positivity
        omega
      _ = 2 ^ prefixDepth e m * y m := hPrefixEq.symm
  have hPow :
      2 ^ (prefixDepth e m + streamDefect e m) <
        2 ^ prefixDepth e m * y m := by
    rw [← hDefectEq]
    exact lt_trans hBeatty hNumerator
  rw [pow_add] at hPow
  exact Nat.lt_of_mul_lt_mul_left hPow

/--
linear boundary defect と recurrence を同時に使う、問題 E 方向の finite package。

block 内の位置 `m=F_n+t` に対し

* `m ≤ K*(defect(m)+1)`
* `2^defect(m) < y_m`

を同時に得る。
-/
theorem interior_linearDefect_and_exponentialEscape
    {e y r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (hRun : RunsOddRecurrence e y)
    {K n t : ℕ}
    (ht : t ≤ r n)
    (hPos : 0 < boundaryIndex r n + t)
    (hNextLinear :
      boundaryIndex r (n + 1) ≤ K * boundaryDefect r (n + 1)) :
    boundaryIndex r n + t ≤
        K * (streamDefect e (boundaryIndex r n + t) + 1) ∧
      2 ^ streamDefect e (boundaryIndex r n + t) <
        y (boundaryIndex r n + t) := by
  exact ⟨
    index_le_mul_streamDefect_add_one_inside hDec ht hNextLinear,
    twoPow_streamDefect_lt_value_inside hDec hRun n t ht hPos
  ⟩

end IntegerReduction
end Collatz3
