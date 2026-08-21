import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyCurrentCorridor

/-!
# Extended critical Beatty phase shift

Stage 8R の corridor 仮定をさらに削るための exact Beatty shift bridge。

既存 `CriticalBeattyCurrentCorridor` は current convergent `(P_j,Q_j)` を使って

* odd `j`:
    `x < P_(j+1)` なら `beta(x) = floor(x Q_j / P_j)`
* even `j`:
    `0 < x < P_(j+1)` なら
    `beta(x) = floor((x Q_j - 1) / P_j)`

を与え、そこから

    P_j + x < P_(j+1)

の狭い範囲で `P_j`-shift periodicity を証明していた。

しかし Stage 8 の residual exponent が非自明になる phase では、必要なのは
より自然な best-approximation window

    0 < x < P_(j+1)

全体での

    beta(P_j + x) = Q_j + beta(x)

である。

ここでは `P_j+x` を一段上の current convergent `j+1` で読む。
actual recurrence

    P_(j+2) = P_j + a_(j+1) P_(j+1),   a_(j+1) > 0

により `x < P_(j+1)` なら `P_j+x < P_(j+2)`。
そのため `CriticalBeattyCurrentCorridor` の `j+1` 版を適用できる。

* odd `j` では `j+1` が even で、Farey determinant

    P_(j+1) Q_j + 1 = P_j Q_(j+1)

  の `+1` が even-current formula の `-1` correction と exact に相殺する。

* even `j` では `j+1` が odd で、Farey determinant

    P_j Q_(j+1) + 1 = P_(j+1) Q_j

  から一つの `-1` が残る。ただし `0 < x < P_(j+1)` では
  `x Q_(j+1)` は `P_(j+1)` の倍数になれない。この nonzero remainder により
  `-1` は quotient を変えず、同じ shift law が得られる。

後半では Stage 8 が直接使う

* current block rise `= Q_j`,
* next block rise `= Q_(j+1)`,
* predecessor one-cell rise の periodicity

を wrapper として公開する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. elementary division helpers -/

/-- positive divisor に対し、上下の倍数で挟めば quotient は一意。 -/
private theorem extended_nat_div_eq_of_mul_bounds
    {n d k : ℕ}
    (hd : 0 < d)
    (hLower : k * d ≤ n)
    (hUpper : n < (k + 1) * d) :
    n / d = k := by
  apply Nat.le_antisymm
  · have hlt : n / d < k + 1 :=
      (Nat.div_lt_iff_lt_mul hd).2 hUpper
    omega
  · exact (Nat.le_div_iff_mul_le hd).2 hLower

/-- `k*d` を numerator に足すと floor quotient は `k` だけ増える。 -/
private theorem extended_add_multiple_div
    (n d k : ℕ)
    (hd : 0 < d) :
    (k * d + n) / d = k + n / d := by
  let q := n / d
  have hLower0 : q * d ≤ n :=
    Nat.div_mul_le_self n d
  have hUpper0 : n < (q + 1) * d := by
    have hq : n / d < n / d + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hd).1 hq
  apply extended_nat_div_eq_of_mul_bounds hd
  · calc
      (k + n / d) * d = k * d + (n / d) * d := by ring
      _ ≤ k * d + n := Nat.add_le_add_left hLower0 _
  · calc
      k * d + n < k * d + (n / d + 1) * d :=
        Nat.add_lt_add_left hUpper0 _
      _ = (k + n / d + 1) * d := by ring

/--
`n mod d > 0` なら numerator から 1 を引いても quotient は変わらない。
これを `k*d` を足した形で使う。
-/
private theorem extended_add_multiple_sub_one_div
    {n d k : ℕ}
    (hd : 0 < d)
    (hmodPos : 0 < n % d) :
    (k * d + n - 1) / d = k + n / d := by
  let q := n / d
  let r := n % d
  have hrPos : 0 < r := by
    simpa [r] using hmodPos
  have hrLt : r < d := by
    dsimp [r]
    exact Nat.mod_lt n hd
  have hDecomp : r + d * q = n := by
    simpa [r, q] using Nat.mod_add_div n d
  have hNum :
      k * d + n - 1 = (k + q) * d + (r - 1) := by
    calc
      k * d + n - 1 = k * d + (r + d * q) - 1 := by rw [hDecomp]
      _ = k * d + (r - 1) + d * q := by omega
      _ = (k + q) * d + (r - 1) := by ring
  apply extended_nat_div_eq_of_mul_bounds hd
  · rw [hNum]
    exact Nat.le_add_right _ _
  · calc
      k * d + n - 1 = (k + q) * d + (r - 1) := hNum
      _ < (k + q) * d + d := by
        exact Nat.add_lt_add_left (by omega) _
      _ = (k + q + 1) * d := by ring

/-! ## 2. recurrence window -/

/--
`x < P_(j+1)` なら `P_j+x < P_(j+2)`。

これは partial quotient の positivity だけを使う。
-/
theorem criticalPowerP_add_lt_nextNext_of_lt_next
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hx : x < criticalPowerP (j + 1)) :
    criticalPowerP j + x < criticalPowerP (j + 2) := by
  have hSpec :=
    actualCriticalPartialQuotient_spec
      (r := j + 1) (by omega : 2 ≤ j + 1)
  have haOne :
      1 ≤ actualCriticalPartialQuotient (j + 1) := by
    exact Nat.succ_le_iff.mpr hSpec.1
  have hPnLe :
      criticalPowerP (j + 1) ≤
        actualCriticalPartialQuotient (j + 1) *
          criticalPowerP (j + 1) := by
    simpa [one_mul] using
      Nat.mul_le_mul_right (criticalPowerP (j + 1)) haOne
  have hRec :
      criticalPowerP (j + 2) =
        criticalPowerP j +
          actualCriticalPartialQuotient (j + 1) *
            criticalPowerP (j + 1) := by
    simpa only [
      show j + 1 + 1 = j + 2 by omega,
      show j + 1 - 1 = j by omega
    ] using hSpec.2.1
  rw [hRec]
  omega

/-! ## 3. odd current index: full positive next-numerator window -/

/--
odd `j` では `x=0` も含めて `x<P_(j+1)` 全域で exact shift。

`P_j+x` は `j+1` の even-current formula で読み、
odd Farey determinant の `+1` と even correction の `-1` を相殺する。
-/
theorem actual_beattyIndex_add_currentP_eq_add_Q_of_odd_extended
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex (criticalPowerP j + x) =
      criticalPowerQ j + beattyIndex x := by
  have hNextEven : (j + 1) % 2 = 0 := by omega
  have hTargetLt :
      criticalPowerP j + x < criticalPowerP (j + 2) :=
    criticalPowerP_add_lt_nextNext_of_lt_next hj hx
  have hTargetPos : 0 < criticalPowerP j + x := by
    have hp : 0 < criticalPowerP j :=
      criticalPowerP_pos (by omega)
    omega
  have hTarget :=
    actual_beattyIndex_eq_current_pred_div_of_even
      (j := j + 1)
      (x := criticalPowerP j + x)
      (by omega)
      hNextEven
      hTargetPos
      (by
        simpa only [show j + 1 + 1 = j + 2 by omega] using hTargetLt)
  have hX :=
    actual_beattyIndex_eq_div
      (j := j + 1)
      (i := x)
      (by omega)
      hx
  have hDet :=
    actualCriticalFareyDeterminant_odd hj hjOdd
  have hNum :
      (criticalPowerP j + x) * criticalPowerQ (j + 1) - 1 =
        criticalPowerQ j * criticalPowerP (j + 1) +
          x * criticalPowerQ (j + 1) := by
    have hSucc :
        (criticalPowerP j + x) * criticalPowerQ (j + 1) =
          criticalPowerQ j * criticalPowerP (j + 1) +
            x * criticalPowerQ (j + 1) + 1 := by
      calc
        (criticalPowerP j + x) * criticalPowerQ (j + 1)
            = criticalPowerP j * criticalPowerQ (j + 1) +
                x * criticalPowerQ (j + 1) := by ring
        _ =
            (criticalPowerP (j + 1) * criticalPowerQ j + 1) +
              x * criticalPowerQ (j + 1) := by
                rw [← hDet]
        _ =
            criticalPowerQ j * criticalPowerP (j + 1) +
              x * criticalPowerQ (j + 1) + 1 := by ring
    omega
  have hPnPos : 0 < criticalPowerP (j + 1) :=
    criticalPowerP_pos (by omega)
  rw [hTarget, hNum]
  rw [extended_add_multiple_div
    (x * criticalPowerQ (j + 1))
    (criticalPowerP (j + 1))
    (criticalPowerQ j)
    hPnPos]
  rw [← hX]

/-! ## 4. even current index: the nonzero-remainder correction -/

/--
`P Qn + 1 = Pn Q` の even Farey orientation の下で、
`0<x<Pn` なら `x*Qn mod Pn` は nonzero。

もし zero なら `Pn | x Qn`。determinant を `x` 倍すると
`Pn | x` まで戻り、`0<x<Pn` に矛盾する。
-/
private theorem even_farey_mul_mod_pos
    {P Q Pn Qn x : ℕ}
    (hPn : 0 < Pn)
    (hxPos : 0 < x)
    (hx : x < Pn)
    (hDet : P * Qn + 1 = Pn * Q) :
    0 < (x * Qn) % Pn := by
  have hModLt : (x * Qn) % Pn < Pn :=
    Nat.mod_lt _ hPn
  by_contra hnot
  have hModZero : (x * Qn) % Pn = 0 := by
    omega
  let t := (x * Qn) / Pn
  have hDecomp0 := Nat.mod_add_div (x * Qn) Pn
  have hDecomp : Pn * t = x * Qn := by
    dsimp [t]
    rw [hModZero] at hDecomp0
    simpa using hDecomp0
  have hEq :
      Pn * (P * t) + x = Pn * (Q * x) := by
    calc
      Pn * (P * t) + x = P * (Pn * t) + x := by ring
      _ = P * (x * Qn) + x := by rw [hDecomp]
      _ = x * (P * Qn + 1) := by ring
      _ = x * (Pn * Q) := by rw [hDet]
      _ = Pn * (Q * x) := by ring
  have hPtLe : P * t ≤ Q * x := by
    by_contra hnotLe
    have hLt : Q * x < P * t := by omega
    have hMulLt :
        Pn * (Q * x) < Pn * (P * t) :=
      (Nat.mul_lt_mul_left hPn).2 hLt
    have hLeftLt :
        Pn * (P * t) < Pn * (P * t) + x := by
      omega
    omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hPtLe
  have hxEq : x = Pn * u := by
    rw [hu, Nat.mul_add] at hEq
    omega
  have hDiv : Pn ∣ x :=
    ⟨u, hxEq⟩
  have hPnLeX : Pn ≤ x :=
    Nat.le_of_dvd hxPos hDiv
  omega

/--
even `j` でも positive domain `0<x<P_(j+1)` 全域で exact shift。

`P_j+x` は `j+1` の odd-current formula で読む。
Farey determinant から numerator に一つ `-1` が残るが、
`even_farey_mul_mod_pos` によりその `-1` は quotient を変えない。
-/
theorem actual_beattyIndex_add_currentP_eq_add_Q_of_even_extended
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hxPos : 0 < x)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex (criticalPowerP j + x) =
      criticalPowerQ j + beattyIndex x := by
  have hNextOdd : (j + 1) % 2 = 1 := by omega
  have hTargetLt :
      criticalPowerP j + x < criticalPowerP (j + 2) :=
    criticalPowerP_add_lt_nextNext_of_lt_next hj hx
  have hTarget :=
    actual_beattyIndex_eq_current_div_of_odd
      (j := j + 1)
      (x := criticalPowerP j + x)
      (by omega)
      hNextOdd
      (by
        simpa only [show j + 1 + 1 = j + 2 by omega] using hTargetLt)
  have hX :=
    actual_beattyIndex_eq_div
      (j := j + 1)
      (i := x)
      (by omega)
      hx
  have hDet :=
    actualCriticalFareyDeterminant_even hj hjEven
  have hPnPos : 0 < criticalPowerP (j + 1) :=
    criticalPowerP_pos (by omega)
  have hModPos :
      0 <
        (x * criticalPowerQ (j + 1)) %
          criticalPowerP (j + 1) :=
    even_farey_mul_mod_pos
      (P := criticalPowerP j)
      (Q := criticalPowerQ j)
      (Pn := criticalPowerP (j + 1))
      (Qn := criticalPowerQ (j + 1))
      (x := x)
      hPnPos hxPos hx hDet
  have hNum :
      (criticalPowerP j + x) * criticalPowerQ (j + 1) =
        criticalPowerQ j * criticalPowerP (j + 1) +
          x * criticalPowerQ (j + 1) - 1 := by
    have hSucc :
        (criticalPowerP j + x) * criticalPowerQ (j + 1) + 1 =
          criticalPowerQ j * criticalPowerP (j + 1) +
            x * criticalPowerQ (j + 1) := by
      calc
        (criticalPowerP j + x) * criticalPowerQ (j + 1) + 1
            = (criticalPowerP j * criticalPowerQ (j + 1) + 1) +
                x * criticalPowerQ (j + 1) := by ring
        _ =
            criticalPowerP (j + 1) * criticalPowerQ j +
              x * criticalPowerQ (j + 1) := by rw [hDet]
        _ =
            criticalPowerQ j * criticalPowerP (j + 1) +
              x * criticalPowerQ (j + 1) := by ring
    omega
  rw [hTarget, hNum]
  rw [extended_add_multiple_sub_one_div
    hPnPos hModPos]
  rw [← hX]

/-! ## 5. parity-free positive-domain theorem -/

/--
Stage 8 用の main extended shift theorem。

`j>=9` かつ `0<x<P_(j+1)` なら parity に依らず

    beta(P_j+x) = Q_j + beta(x).

旧 theorem の `P_j+x<P_(j+1)` を `x<P_(j+1)` まで拡張する。
-/
theorem actual_beattyIndex_add_currentP_eq_add_Q_of_pos_lt_nextP
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hxPos : 0 < x)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex (criticalPowerP j + x) =
      criticalPowerQ j + beattyIndex x := by
  have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · exact
      actual_beattyIndex_add_currentP_eq_add_Q_of_odd_extended
        hj hjOdd hx
  · have hjEven : j % 2 = 0 := by omega
    exact
      actual_beattyIndex_add_currentP_eq_add_Q_of_even_extended
        hj hjEven hxPos hx

/-! ## 6. Stage 8 wrappers -/

/--
positive phase `x<P_(j+1)` では scale `j` block の Beatty rise は exact `Q_j`。
-/
theorem actual_beattyIndex_currentP_rise_eq_Q_of_pos_lt_nextP
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hxPos : 0 < x)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex (x + criticalPowerP j) - beattyIndex x =
      criticalPowerQ j := by
  have hShift :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_pos_lt_nextP
      hj hxPos hx
  rw [Nat.add_comm] at hShift
  omega

/--
同じ `x<P_(j+1)` から next scale `j+1` の rise も exact に得られる。
`P_(j+1)<P_(j+2)` なので extended theorem を一段進めるだけ。
-/
theorem actual_beattyIndex_nextP_rise_eq_nextQ_of_pos_lt_nextP
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hxPos : 0 < x)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex (x + criticalPowerP (j + 1)) - beattyIndex x =
      criticalPowerQ (j + 1) := by
  have hNextPLt :
      criticalPowerP (j + 1) < criticalPowerP (j + 2) :=
    criticalPowerP_strict_succ (r := j + 1) (by omega)
  have hxNext : x < criticalPowerP (j + 2) :=
    lt_trans hx hNextPLt
  have hShift :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_pos_lt_nextP
      (j := j + 1)
      (x := x)
      (by omega)
      hxPos
      hxNext
  rw [Nat.add_comm] at hShift
  omega

/--
`2≤x<P_(j+1)` なら scale `j` shift は predecessor one-cell Beatty rise を保存する。

これは criticalization-start nonreturn で必要な

  beta(x+P_j)-beta(x+P_j-1) = beta(x)-beta(x-1)

を corridor 仮定なしで供給する。
-/
theorem actual_beattyIndex_currentP_preserves_pred_cell_of_two_le_lt_nextP
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hxTwo : 2 ≤ x)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex (x + criticalPowerP j) -
        beattyIndex (x + criticalPowerP j - 1) =
      beattyIndex x - beattyIndex (x - 1) := by
  have hxPos : 0 < x := by omega
  have hxPredPos : 0 < x - 1 := by omega
  have hxPred : x - 1 < criticalPowerP (j + 1) := by omega
  have hShift :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_pos_lt_nextP
      (j := j) (x := x) hj hxPos hx
  have hShiftPred0 :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_pos_lt_nextP
      (j := j) (x := x - 1) hj hxPredPos hxPred
  have hIndex :
      criticalPowerP j + (x - 1) =
        x + criticalPowerP j - 1 := by
    omega
  have hShiftPred :
      beattyIndex (x + criticalPowerP j - 1) =
        criticalPowerQ j + beattyIndex (x - 1) := by
    rw [← hIndex]
    exact hShiftPred0
  have hShift' :
      beattyIndex (x + criticalPowerP j) =
        criticalPowerQ j + beattyIndex x := by
    simpa [Nat.add_comm] using hShift
  rw [hShift', hShiftPred]
  omega

end ExternalArithmetic
end CSTMicro
end Collatz2
