import CollatzLean.CollatzFirstLayer.CanonicalReplay
import CollatzLean.CollatzFirstLayer.SignedReplay

import Mathlib.Tactic.Linarith

/-!
# negative shadowのcanonical re-anchoring

canonical actual runのpredecessor shadowを1回signed odd stepで進めたとき、
その新しいnegative shadowを、指数を1個appendしたcanonical wordの
predecessor shadowとして再配置する。

このファイルは元のpositive orbitへの再接続を主張しない。
保存するのは、negative center、canonical actual run、shadow生成方程式である。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- singleton append後のresidue modulus。 -/
theorem residueModulus_append_singleton
    (w : ExpWord) (e : ℕ) :
    residueModulus (w ++ [e]) =
      residueModulus w * 2 ^ e := by
  unfold residueModulus
  rw [twoSteps_append]
  have hsingleton : twoSteps [e] = e := by
    simp [twoSteps]
  rw [hsingleton]
  rw [show twoSteps w + e + 1 = (twoSteps w + 1) + e by omega]
  exact pow_add 2 (twoSteps w + 1) e

namespace Runs

/-- 二つのactual runを連結する。 -/
theorem append_runs
    {u v : ExpWord} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z) :
    Runs (u ++ v) x z := by
  induction hu with
  | nil x =>
      simpa using hv
  | @cons e u x y₀ y he hstep hy htail ih =>
      exact Runs.cons he hstep hy (ih hv)

end Runs

/--
一つのnegative predecessor shadowに対するexactなsigned odd step。

`currentMagnitude`、`nextMagnitude`はいずれも正で、
`2^exponent * nextMagnitude + 1 = 3 * currentMagnitude`
がnegative側の式
`2^exponent * (-nextMagnitude) = 3 * (-currentMagnitude) + 1`
を表す。
-/
structure NegativeShadowStepData (w : ExpWord) where
  currentMagnitude : ℕ
  current_pos : 0 < currentMagnitude
  currentShadow_eq :
    predecessorShadow w = -(currentMagnitude : ℤ)
  exponent : ℕ
  exponent_pos : 0 < exponent
  nextMagnitude : ℕ
  next_pos : 0 < nextMagnitude
  next_odd : Odd nextMagnitude
  stepEquation :
    2 ^ exponent * nextMagnitude + 1 =
      3 * currentMagnitude

/--
negative shadowを1段進めた後のcanonical re-anchoring。

新しいcanonical wordは`w ++ [exponent]`であり、
predecessor startは元のwordとexactに同じである。
-/
structure ShadowReanchoringStepData
    (w : ExpWord) (S : NegativeShadowStepData w) where
  start : ℕ
  finish : ℕ
  runs : Runs (w ++ [S.exponent]) start finish
  start_eq_canonical :
    start = canonicalStart (w ++ [S.exponent])
  finish_eq_canonical :
    finish = canonicalEnd (w ++ [S.exponent])
  predecessorStart_eq :
    predecessorStart (w ++ [S.exponent]) = predecessorStart w
  predecessorShadow_eq :
    predecessorShadow (w ++ [S.exponent]) =
      -(S.nextMagnitude : ℤ)

/--
current negative shadowの大きさとcanonical endpointの和。
-/
private theorem negativeShadow_currentEnd_add_magnitude
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    canonicalEnd w + S.currentMagnitude =
      2 * 3 ^ oddSteps w := by
  have hz :
      (canonicalEnd w : ℤ) + (S.currentMagnitude : ℤ) =
        2 * (3 : ℤ) ^ oddSteps w := by
    have hs := S.currentShadow_eq
    unfold predecessorShadow at hs
    omega
  exact_mod_cast hz


/--
正の指数に対する`2 ^ e`の最小値。
-/
private theorem two_le_twoPow_of_pos
    {e : ℕ}
    (he : 0 < e) :
    2 ≤ 2 ^ e := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, e = r + 1 := by
    exact ⟨e - 1, by omega⟩
  rw [hr, pow_succ]
  have hone : 1 ≤ 2 ^ r := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (by omega)))
  omega


/--
current negative shadowの大きさは、
現在のcanonical scaleより真に小さい。
-/
private theorem negativeShadow_currentMagnitude_lt_scale
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    S.currentMagnitude < 2 * 3 ^ oddSteps w := by
  have hsum :=
    negativeShadow_currentEnd_add_magnitude S
  have hend :
      0 < canonicalEnd w :=
    canonicalEnd_pos w
  omega


/--
negative shadowのexact step equationから、
scaled next magnitudeはcurrent magnitudeの3倍より小さい。
-/
private theorem negativeShadow_scaledNext_lt_threeCurrent
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    2 ^ S.exponent * S.nextMagnitude <
      3 * S.currentMagnitude := by
  have hstep := S.stepEquation
  omega


/--
scaled next magnitudeとcurrent scaleの上界から、
next magnitudeを次の3進scaleで抑える純粋な算術補題。
-/
private theorem nextMagnitude_lt_threePow_succ_of_scaled_bounds
    {q e currentMagnitude nextMagnitude : ℕ}
    (hpowTwo :
      2 ≤ 2 ^ e)
    (hstepLt :
      2 ^ e * nextMagnitude <
        3 * currentMagnitude)
    (hcurrentLt :
      currentMagnitude <
        2 * 3 ^ q) :
    nextMagnitude < 3 ^ (q + 1) := by
  have hnextScaled :
      2 * nextMagnitude ≤
        2 ^ e * nextMagnitude := by
    exact
      Nat.mul_le_mul_right
        nextMagnitude
        hpowTwo
  have hcurrentScaled :
      3 * currentMagnitude <
        3 * (2 * 3 ^ q) := by
    exact
      (Nat.mul_lt_mul_left
        (a := 3)
        (by omega)).2
        hcurrentLt
  rw [pow_succ]
  omega


/--
negative shadowのexact step後の大きさは、
次の3進canonical scaleより真に小さい。
-/
private theorem negativeShadow_nextMagnitude_lt_threePow
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    S.nextMagnitude < 3 ^ (oddSteps w + 1) := by
  exact
    nextMagnitude_lt_threePow_succ_of_scaled_bounds
      (two_le_twoPow_of_pos S.exponent_pos)
      (negativeShadow_scaledNext_lt_threeCurrent S)
      (negativeShadow_currentMagnitude_lt_scale S)


/--
次のcanonical候補endpointとnext shadow magnitudeの和。
-/
private theorem negativeShadow_nextFinish_add_magnitude
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    (2 * 3 ^ (oddSteps w + 1) - S.nextMagnitude) +
        S.nextMagnitude =
      2 * 3 ^ (oddSteps w + 1) := by
  have hNextLt :=
    negativeShadow_nextMagnitude_lt_threePow S
  omega


/--
次のcanonical候補endpointは奇数。
-/
private theorem negativeShadow_nextFinish_odd
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    Odd
      (2 * 3 ^ (oddSteps w + 1) -
        S.nextMagnitude) := by
  have hNextLt :=
    negativeShadow_nextMagnitude_lt_threePow S
  rcases S.next_odd with ⟨a, ha⟩
  refine
    ⟨3 ^ (oddSteps w + 1) - a - 1, ?_⟩
  omega


/--
replay終了点から次のcanonical候補endpointへのexact Collatz step。
-/
private theorem negativeShadow_reanchor_exact_step
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    2 ^ S.exponent *
        (2 * 3 ^ (oddSteps w + 1) -
          S.nextMagnitude) =
      3 *
          (canonicalEnd w +
            2 * 3 ^ oddSteps w *
              (2 ^ S.exponent - 1)) +
        1 := by
  let k : ℕ := 2 ^ S.exponent - 1
  let replayFinish : ℕ :=
    canonicalEnd w + 2 * 3 ^ oddSteps w * k
  let nextFinish : ℕ :=
    2 * 3 ^ (oddSteps w + 1) -
      S.nextMagnitude
  have hpowPos :
      0 < 2 ^ S.exponent := by
    exact Nat.pow_pos (by omega)
  have hk :
      2 ^ S.exponent = k + 1 := by
    dsimp [k]
    omega
  have hCurrentSum :=
    negativeShadow_currentEnd_add_magnitude S
  have hNextFinishSum :
      nextFinish + S.nextMagnitude =
        2 * 3 ^ (oddSteps w + 1) := by
    dsimp [nextFinish]
    exact negativeShadow_nextFinish_add_magnitude S
  have hleft :
      2 ^ S.exponent * nextFinish +
          2 ^ S.exponent * S.nextMagnitude =
        2 ^ S.exponent *
          (2 * 3 ^ (oddSteps w + 1)) := by
    rw [← Nat.mul_add, hNextFinishSum]
  have hright :
      (3 * replayFinish + 1) +
          2 ^ S.exponent * S.nextMagnitude =
        2 ^ S.exponent *
          (2 * 3 ^ (oddSteps w + 1)) := by
    calc
      (3 * replayFinish + 1) +
            2 ^ S.exponent * S.nextMagnitude
          =
        3 * canonicalEnd w +
            6 * 3 ^ oddSteps w * k +
            (2 ^ S.exponent *
                S.nextMagnitude + 1) := by
              dsimp [replayFinish]
              ring
      _ =
        3 * canonicalEnd w +
            6 * 3 ^ oddSteps w * k +
            3 * S.currentMagnitude := by
              rw [S.stepEquation]
      _ =
        3 *
            (canonicalEnd w +
              S.currentMagnitude) +
            6 * 3 ^ oddSteps w * k := by
              ring
      _ =
        6 * 3 ^ oddSteps w +
            6 * 3 ^ oddSteps w * k := by
              rw [hCurrentSum]
              ring
      _ =
        6 * 3 ^ oddSteps w * (k + 1) := by
              ring
      _ =
        2 ^ S.exponent *
            (2 * 3 ^ (oddSteps w + 1)) := by
              rw [← hk, pow_succ]
              ring
  have hstep :
      2 ^ S.exponent * nextFinish =
        3 * replayFinish + 1 := by
    exact
      Nat.add_right_cancel
        (hleft.trans hright.symm)
  simpa [replayFinish, nextFinish, k] using hstep


/--
canonical runをreplayし、negative-shadow exact stepを1つ追加する。
-/
private theorem negativeShadow_reanchor_runs
    {w : ExpWord}
    (hRun : Runs w (canonicalStart w) (canonicalEnd w))
    (S : NegativeShadowStepData w) :
    Runs
      (w ++ [S.exponent])
      (canonicalStart w +
        residueModulus w *
          (2 ^ S.exponent - 1))
      (2 * 3 ^ (oddSteps w + 1) -
        S.nextMagnitude) := by
  let k : ℕ := 2 ^ S.exponent - 1
  let nextStart : ℕ :=
    canonicalStart w + residueModulus w * k
  let replayFinish : ℕ :=
    canonicalEnd w + 2 * 3 ^ oddSteps w * k
  let nextFinish : ℕ :=
    2 * 3 ^ (oddSteps w + 1) -
      S.nextMagnitude
  have hReplay :
      Runs w nextStart replayFinish := by
    dsimp [nextStart, replayFinish]
    simpa [residueModulus] using
      hRun.replay (k := k)
  have hStep :
      2 ^ S.exponent * nextFinish =
        3 * replayFinish + 1 := by
    simpa [nextFinish, replayFinish, k] using
      negativeShadow_reanchor_exact_step S
  have hNextOdd :
      Odd nextFinish := by
    dsimp [nextFinish]
    exact negativeShadow_nextFinish_odd S
  have hSingle :
      Runs [S.exponent] replayFinish nextFinish := by
    exact
      Runs.cons
        S.exponent_pos
        hStep
        hNextOdd
        (Runs.nil nextFinish)
  have hExtended :
      Runs
        (w ++ [S.exponent])
        nextStart
        nextFinish :=
    Runs.append_runs hReplay hSingle
  simpa [nextStart, nextFinish, k] using hExtended


/--
re-anchoring後の開始点は、新しい語のresidue modulus未満。
-/
private theorem negativeShadow_reanchor_start_lt_modulus
    {w : ExpWord}
    (S : NegativeShadowStepData w) :
    canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1) <
      residueModulus (w ++ [S.exponent]) := by
  let M : ℕ := residueModulus w
  let k : ℕ := 2 ^ S.exponent - 1
  have hpowPos :
      0 < 2 ^ S.exponent := by
    exact Nat.pow_pos (by omega)
  have hk :
      2 ^ S.exponent = k + 1 := by
    dsimp [k]
    omega
  have hModulus :
      residueModulus (w ++ [S.exponent]) =
        M * 2 ^ S.exponent := by
    simpa [M] using
      residueModulus_append_singleton w S.exponent
  rw [hModulus, hk]
  dsimp [M, k]
  calc
    canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1)
        <
      residueModulus w +
          residueModulus w *
            (2 ^ S.exponent - 1) := by
              exact
                Nat.add_lt_add_right
                  (canonicalStart_lt_modulus w)
                  (residueModulus w *
                    (2 ^ S.exponent - 1))
    _ =
      residueModulus w *
        ((2 ^ S.exponent - 1) + 1) := by
          ring


/--
re-anchoring後の開始点は、新しい語のcanonical start。
-/
private theorem negativeShadow_reanchor_start_eq_canonical
    {w : ExpWord}
    (S : NegativeShadowStepData w)
    (hExtended :
      Runs
        (w ++ [S.exponent])
        (canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1))
        (2 * 3 ^ (oddSteps w + 1) -
          S.nextMagnitude)) :
    canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1) =
      canonicalStart (w ++ [S.exponent]) := by
  let nextStart : ℕ :=
    canonicalStart w +
      residueModulus w *
        (2 ^ S.exponent - 1)
  let nextFinish : ℕ :=
    2 * 3 ^ (oddSteps w + 1) -
      S.nextMagnitude
  have hNextOdd :
      Odd nextFinish := by
    dsimp [nextFinish]
    exact negativeShadow_nextFinish_odd S
  have hStartLt :
      nextStart <
        residueModulus (w ++ [S.exponent]) := by
    dsimp [nextStart]
    exact negativeShadow_reanchor_start_lt_modulus S
  have hmod :=
    natural_start_mod_eq_canonicalStart
      hExtended.realizes
      hNextOdd
  calc
    nextStart =
        nextStart %
          residueModulus (w ++ [S.exponent]) := by
            symm
            exact Nat.mod_eq_of_lt hStartLt
    _ =
      canonicalStart (w ++ [S.exponent]) := hmod


/--
re-anchoring後の終了点は、新しい語のcanonical end。
-/
private theorem negativeShadow_reanchor_finish_eq_canonical
    {w : ExpWord}
    (S : NegativeShadowStepData w)
    (hExtended :
      Runs
        (w ++ [S.exponent])
        (canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1))
        (2 * 3 ^ (oddSteps w + 1) -
          S.nextMagnitude))
    (hStartEq :
      canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1) =
        canonicalStart (w ++ [S.exponent])) :
    2 * 3 ^ (oddSteps w + 1) -
          S.nextMagnitude =
      canonicalEnd (w ++ [S.exponent]) := by
  let C :=
    canonicalReplayCoordinate_of_runs
      hExtended
      (by simp)
  have hzero :
      C.quotient = 0 := by
    exact
      C.quotient_eq_zero_of_start_eq_canonical
        hStartEq
  have hfinish := C.finish_eq
  rw [hzero] at hfinish
  simpa using hfinish


/--
re-anchoringはpredecessor startを保存する。
-/
private theorem negativeShadow_reanchor_predecessorStart_eq
    {w : ExpWord}
    (S : NegativeShadowStepData w)
    (hStartEq :
      canonicalStart w +
          residueModulus w *
            (2 ^ S.exponent - 1) =
        canonicalStart (w ++ [S.exponent])) :
    predecessorStart (w ++ [S.exponent]) =
      predecessorStart w := by
  have hpowPos :
      0 < 2 ^ S.exponent := by
    exact Nat.pow_pos (by omega)
  have hk :
      2 ^ S.exponent =
        (2 ^ S.exponent - 1) + 1 := by
    omega
  have hModulus :
      residueModulus (w ++ [S.exponent]) =
        residueModulus w * 2 ^ S.exponent := by
    exact
      residueModulus_append_singleton
        w
        S.exponent
  unfold predecessorStart
  rw [← hStartEq, hModulus, hk]
  push_cast
  ring


/--
re-anchoring後のpredecessor shadowは、
次のnegative magnitudeと一致する。
-/
private theorem negativeShadow_reanchor_predecessorShadow_eq
    {w : ExpWord}
    (S : NegativeShadowStepData w)
    (hFinishEq :
      2 * 3 ^ (oddSteps w + 1) -
          S.nextMagnitude =
        canonicalEnd (w ++ [S.exponent])) :
    predecessorShadow (w ++ [S.exponent]) =
      -(S.nextMagnitude : ℤ) := by
  have hNextFinishSum :=
    negativeShadow_nextFinish_add_magnitude S
  have hz :
      ((2 * 3 ^ (oddSteps w + 1) -
          S.nextMagnitude : ℕ) : ℤ) -
          2 * (3 : ℤ) ^ (oddSteps w + 1) =
        -(S.nextMagnitude : ℤ) := by
    have hsumZ :
        ((2 * 3 ^ (oddSteps w + 1) -
            S.nextMagnitude : ℕ) : ℤ) +
            (S.nextMagnitude : ℤ) =
          2 * (3 : ℤ) ^ (oddSteps w + 1) := by
      exact_mod_cast hNextFinishSum
    omega
  unfold predecessorShadow
  rw [← hFinishEq]
  simpa [oddSteps_append, oddSteps] using hz


/--
canonical actual runとnegative shadowのexact stepから、
次のcanonical re-anchoringを構成する。
-/
noncomputable def reanchorNegativeShadowStep
    {w : ExpWord}
    (hRun : Runs w (canonicalStart w) (canonicalEnd w))
    (S : NegativeShadowStepData w) :
    ShadowReanchoringStepData w S := by
  let nextStart : ℕ :=
    canonicalStart w +
      residueModulus w *
        (2 ^ S.exponent - 1)
  let nextFinish : ℕ :=
    2 * 3 ^ (oddSteps w + 1) -
      S.nextMagnitude
  have hExtended :
      Runs
        (w ++ [S.exponent])
        nextStart
        nextFinish := by
    simpa [nextStart, nextFinish] using
      negativeShadow_reanchor_runs hRun S
  have hStartEq :
      nextStart =
        canonicalStart (w ++ [S.exponent]) := by
    simpa [nextStart, nextFinish] using
      negativeShadow_reanchor_start_eq_canonical
        S
        hExtended
  have hFinishEq :
      nextFinish =
        canonicalEnd (w ++ [S.exponent]) := by
    simpa [nextStart, nextFinish] using
      negativeShadow_reanchor_finish_eq_canonical
        S
        hExtended
        hStartEq
  have hPredecessorStart :
      predecessorStart (w ++ [S.exponent]) =
        predecessorStart w := by
    simpa [nextStart] using
      negativeShadow_reanchor_predecessorStart_eq
        S
        hStartEq
  have hPredecessorShadow :
      predecessorShadow (w ++ [S.exponent]) =
        -(S.nextMagnitude : ℤ) := by
    simpa [nextFinish] using
      negativeShadow_reanchor_predecessorShadow_eq
        S
        hFinishEq
  exact
    { start := nextStart
      finish := nextFinish
      runs := hExtended
      start_eq_canonical := hStartEq
      finish_eq_canonical := hFinishEq
      predecessorStart_eq := hPredecessorStart
      predecessorShadow_eq := hPredecessorShadow }

end ExpWord
end CollatzFirstLayer
