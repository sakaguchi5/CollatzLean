import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalSuffixTransport
import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalCarryPattern
import CollatzLean.CollatzWindowCore.NormalizationFromWindow

import Mathlib.Data.Finset.Basic

/-!
# Constant terminal normalization depth patternの固定

terminal time `T`が固定されると、normalization差深さも有限範囲へ入る。

* capture時は現在depthが固定lower exponent未満
* synchronized時は現在depth = lower exponent + 次時刻depth
* terminalではdepth = terminal lower exponent

したがって各時刻のdepthは固定prefix指数の有限和で一様に抑えられる。
この有限範囲を`Fin`へ符号化し、carry pattern固定後の無限部分列をさらに選んで
terminal以前を含むdepth pattern全体を固定する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 同じactual window差を表す完全2進分解のdepthは一意。 -/
private theorem windowDifference_depth_unique
    {O : OddOrbit} {i q : ℕ}
    (D E : O.WindowDifferenceData i q) :
    D.depth = E.depth := by
  have hmul :
      2 ^ D.depth * D.oddPart = 2 ^ E.depth * E.oddPart := by
    have hD := D.difference
    have hE := E.difference
    omega
  have hDfac :
      ExactTwoFactor
        (2 ^ D.depth * D.oddPart)
        D.depth D.oddPart :=
    ⟨rfl, D.oddPart_odd⟩
  have hEfac :
      ExactTwoFactor
        (2 ^ D.depth * D.oddPart)
        E.depth E.oddPart :=
    ⟨hmul, E.oddPart_odd⟩
  exact exactTwoFactor_exponent_unique hDfac hEfac

/-- synchronized carryではcurrent depthはlower exponentとnext depthの和。 -/
private theorem synchronized_depth_eq_lower_add_next
    {O : OddOrbit} {i q : ℕ}
    (S : O.SynchronizedWindowAt i q)
    (N : O.WindowDifferenceData (i + 1) q) :
    S.depth = O.exponent i + N.depth := by
  let C : O.WindowDifferenceData (i + 1) q :=
    { depth := S.depth - O.exponent i
      oddPart := 3 * S.oddPart
      difference := by
        have h := S.upperNext_eq
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      oddPart_odd :=
        (show Odd (3 : ℕ) by decide).mul S.oddPart_odd }
  have hDepth : C.depth = N.depth :=
    windowDifference_depth_unique C N
  have hlt := S.synchronized
  dsimp [C] at hDepth
  omega

namespace FutureMinimumSpecialC3TowerData
namespace ConstantTerminalNestedAlignmentData

/-- selected normalizationのterminal timeはConstant値に一致。 -/
theorem selectedNormalization_terminalTime_eq
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    (R.normalization (D.selectedIndex n)).terminalTime =
      D.terminal.value := by
  change R.terminalTime (D.selectedIndex n) = D.terminal.value
  simpa [selectedIndex] using D.terminal.value_eq n

/-- terminalまでのlower exponentを全部支配する固定有限量。 -/
def fixedPrefixExponentBound
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) : ℕ :=
  Finset.sum (Finset.range (D.terminal.value + 1))
    (fun t => O.exponent (R.anchor + t))

/-- terminal以前を含む各lower exponentは固定prefix bound以下。 -/
theorem lowerExponent_le_fixedPrefixExponentBound
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (t : ℕ)
    (ht : t ≤ D.terminal.value) :
    O.exponent (R.anchor + t) ≤ D.fixedPrefixExponentBound := by
  unfold fixedPrefixExponentBound
  exact
    Finset.single_le_sum
      (fun k (_hk : k ∈ Finset.range (D.terminal.value + 1)) =>
        Nat.zero_le (O.exponent (R.anchor + k)))
      (Finset.mem_range.mpr (by omega))

/-- n番目のnormalizationにおける時刻`t≤T`のdifference depth。 -/
noncomputable def normalizationDepth
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ)
    (t : Fin (D.terminal.value + 1)) : ℕ :=
  ((R.normalization (D.selectedIndex n)).difference t.1 (by
    rw [D.selectedNormalization_terminalTime_eq n]
    omega)).depth

/--
開始位置が等しい二つのwindow difference dataは同じdepthを持つ。
依存型のstart輸送をこの補題内に隔離する。
-/
private theorem windowDifference_depth_unique_of_start_eq
    {O : OddOrbit}
    {start₁ start₂ length : ℕ}
    (hStart : start₁ = start₂)
    (D₁ : O.WindowDifferenceData start₁ length)
    (D₂ : O.WindowDifferenceData start₂ length) :
    D₁.depth = D₂.depth := by
  subst start₂
  exact windowDifference_depth_unique D₁ D₂

/--
selected normalizationのterminal difference depthは、
terminal位置のactual exponentそのもの。
-/
private theorem normalizationDepth_at_terminal_eq_lowerExponent
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    ((R.normalization (D.selectedIndex n)).difference
      D.terminal.value
      (by
        rw [D.selectedNormalization_terminalTime_eq n])).depth =
      O.exponent (R.anchor + D.terminal.value) := by
  let N :=
    R.normalization (D.selectedIndex n)
  have hTime :
      N.terminalTime = D.terminal.value := by
    simpa [N] using
      D.selectedNormalization_terminalTime_eq n
  let Dterm :=
    (R.normalization (D.selectedIndex n)).difference
      D.terminal.value
      (by
        rw [D.selectedNormalization_terminalTime_eq n])
  have hStart :
      R.anchor + D.terminal.value =
        R.anchor + N.terminalTime := by
    rw [hTime]
  have hDepth :
      Dterm.depth = N.terminal.depth := by
    exact
      windowDifference_depth_unique_of_start_eq
        hStart
        Dterm
        N.terminal.toWindowDifferenceData
  have hDeferred :
      N.terminal.depth =
        O.exponent (R.anchor + D.terminal.value) := by
    calc
      N.terminal.depth
          = O.exponent (R.anchor + N.terminalTime) :=
        N.terminal.deferred
      _ = O.exponent (R.anchor + D.terminal.value) := by
        rw [hTime]
  have hResult :
      Dterm.depth =
        O.exponent (R.anchor + D.terminal.value) :=
    hDepth.trans hDeferred
  simpa [Dterm] using hResult


/--
selected normalizationのterminal depthは、
固定prefix exponent bound以下。
-/
private theorem normalizationDepth_at_terminal_le
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    ((R.normalization (D.selectedIndex n)).difference
      D.terminal.value
      (by
        rw [D.selectedNormalization_terminalTime_eq n])).depth ≤
      D.fixedPrefixExponentBound := by
  have hDepth :=
    normalizationDepth_at_terminal_eq_lowerExponent D n
  have hLower :=
    D.lowerExponent_le_fixedPrefixExponentBound
      D.terminal.value
      le_rfl
  calc
    ((R.normalization (D.selectedIndex n)).difference
      D.terminal.value
      (by
        rw [D.selectedNormalization_terminalTime_eq n])).depth
        =
      O.exponent (R.anchor + D.terminal.value) := hDepth
    _ ≤ D.fixedPrefixExponentBound := hLower


/--
固定bound一個分は、任意の`r`について
`(r+2)`個分以下。
-/
private theorem fixedPrefixExponentBound_le_succ_mul
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (r : ℕ) :
    D.fixedPrefixExponentBound ≤
      (r + 2) * D.fixedPrefixExponentBound := by
  have hfac :
      1 ≤ r + 2 := by
    omega
  simpa using
    Nat.mul_le_mul_right
      D.fixedPrefixExponentBound
      hfac


/--
terminalから`r`時刻戻ったdepthが既に評価されているなら、
さらに1時刻戻ったdepthは`(r+2)`倍bound以下。

capture枝では現在depthを直接boundし、
synchronized枝では
`currentDepth = lowerExponent + nextDepth`
を使う。
-/
private theorem normalizationDepth_sub_succ_le
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n r : ℕ)
    (_hr0 : r ≤ D.terminal.value)
    (hrSucc : r + 1 ≤ D.terminal.value)
    (hPrev :
      ((R.normalization (D.selectedIndex n)).difference
        (D.terminal.value - r)
        (by
          rw [D.selectedNormalization_terminalTime_eq n]
          omega)).depth ≤
        (r + 1) * D.fixedPrefixExponentBound) :
    ((R.normalization (D.selectedIndex n)).difference
      (D.terminal.value - (r + 1))
      (by
        rw [D.selectedNormalization_terminalTime_eq n]
        omega)).depth ≤
      (r + 2) * D.fixedPrefixExponentBound := by
  let t := D.terminal.value - (r + 1)
  have htlt :
      t < D.terminal.value := by
    dsimp [t]
    omega
  let N :=
    R.normalization (D.selectedIndex n)
  have hTime :
      N.terminalTime = D.terminal.value := by
    simpa [N] using
      D.selectedNormalization_terminalTime_eq n
  let Dcur :=
    N.difference t
      (by
        simpa [hTime] using
          Nat.le_of_lt htlt)
  have hBefore :=
    N.before t
      (by
        simpa [hTime] using htlt)
  rcases hBefore with ⟨C | S⟩
  ·-- capture枝
    have hDepth :
        Dcur.depth = C.depth :=
      windowDifference_depth_unique
        Dcur
        C.toWindowDifferenceData
    have hLower :=
      D.lowerExponent_le_fixedPrefixExponentBound
        t
        (by omega)
    have hBound :=
      fixedPrefixExponentBound_le_succ_mul
        D r
    calc
      ((R.normalization (D.selectedIndex n)).difference
        (D.terminal.value - (r + 1))
        (by
          rw [D.selectedNormalization_terminalTime_eq n]
          omega)).depth
          =
        Dcur.depth := by
          rfl
      _ = C.depth := hDepth
      _ ≤ O.exponent (R.anchor + t) :=
        Nat.le_of_lt C.captured
      _ ≤ D.fixedPrefixExponentBound :=
        hLower
      _ ≤
          (r + 2) * D.fixedPrefixExponentBound :=
        hBound
  ·-- synchronized枝
    let Dnext :=
      N.difference (t + 1)
        (by
          rw [hTime]
          omega)
    have hDepth :
        Dcur.depth = S.depth :=
      windowDifference_depth_unique
        Dcur
        S.toWindowDifferenceData
    have hRec0 :=
      synchronized_depth_eq_lower_add_next
        S
        (by
          simpa [Nat.add_assoc] using Dnext)
    have hRec :
        S.depth =
          O.exponent (R.anchor + t) +
            Dnext.depth := by
      simpa [Nat.add_assoc] using hRec0
    have hLower :=
      D.lowerExponent_le_fixedPrefixExponentBound
        t
        (by omega)
    have hIndex :
        t + 1 =
          D.terminal.value - r := by
      dsimp [t]
      omega
    let Dprev :=
      N.difference
        (D.terminal.value - r)
        (by
          rw [hTime]
          omega)
    have hPrev' :
        Dprev.depth ≤
          (r + 1) * D.fixedPrefixExponentBound := by
      simpa [Dprev, N] using hPrev
    have hStartEq :
        R.anchor + (t + 1) =
          R.anchor + (D.terminal.value - r) := by
      rw [hIndex]
    have hDepthNextPrev :
        Dnext.depth = Dprev.depth := by
      exact
        windowDifference_depth_unique_of_start_eq
          hStartEq
          Dnext
          Dprev
    have hNext :
        Dnext.depth ≤
          (r + 1) * D.fixedPrefixExponentBound := by
      calc
        Dnext.depth
            = Dprev.depth := hDepthNextPrev
        _ ≤
            (r + 1) * D.fixedPrefixExponentBound := hPrev'
    calc
      ((R.normalization (D.selectedIndex n)).difference
        (D.terminal.value - (r + 1))
        (by
          rw [D.selectedNormalization_terminalTime_eq n]
          omega)).depth
          =
        Dcur.depth := by
          rfl
      _ = S.depth := hDepth
      _ =
          O.exponent (R.anchor + t) +
            Dnext.depth := hRec
      _ ≤
          D.fixedPrefixExponentBound +
            (r + 1) *
              D.fixedPrefixExponentBound :=
        Nat.add_le_add hLower hNext
      _ =
          (r + 2) *
            D.fixedPrefixExponentBound := by
        ring


/--
terminalから`r`時刻だけ戻ったdifference depthは、
`(r+1) * fixedPrefixExponentBound`以下。
-/
private theorem normalizationDepth_sub_le
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n r : ℕ)
    (hr : r ≤ D.terminal.value) :
    ((R.normalization (D.selectedIndex n)).difference
      (D.terminal.value - r)
      (by
        rw [D.selectedNormalization_terminalTime_eq n]
        omega)).depth ≤
      (r + 1) * D.fixedPrefixExponentBound := by
  revert hr
  induction r with
  | zero =>
      intro _
      have hTerminal :=
        normalizationDepth_at_terminal_le D n
      simpa using hTerminal
  | succ r ih =>
      intro hr
      have hr0 :
          r ≤ D.terminal.value := by
        omega
      have hPrev :=
        ih hr0
      have hStep :=
        normalizationDepth_sub_succ_le
          D n r
          hr0
          (by
            simpa using hr)
          hPrev
      simpa [Nat.succ_eq_add_one] using hStep

/-- 全normalization depthを支配する一つの固定有限上界。 -/
def normalizationDepthBound
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) : ℕ :=
  (D.terminal.value + 1) * D.fixedPrefixExponentBound

/-- terminal以前を含む全depthは固定bound以下。 -/
theorem normalizationDepth_le_bound
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ)
    (t : Fin (D.terminal.value + 1)) :
    D.normalizationDepth n t ≤ D.normalizationDepthBound := by
  let r := D.terminal.value - t.1
  have hr :
      r ≤ D.terminal.value := by
    dsimp [r]
    omega
  have hPrev :=
    D.normalizationDepth_sub_le n r hr
  have hindex :
      D.terminal.value - r = t.1 := by
    dsimp [r]
    omega
  let Dsub :=
    (R.normalization (D.selectedIndex n)).difference
      (D.terminal.value - r)
      (by
        rw [D.selectedNormalization_terminalTime_eq n]
        omega)
  let Dt :=
    (R.normalization (D.selectedIndex n)).difference
      t.1
      (by
        rw [D.selectedNormalization_terminalTime_eq n]
        exact Nat.le_of_lt_succ t.2)
  have hPrev' :
      Dsub.depth ≤
        (r + 1) * D.fixedPrefixExponentBound := by
    simpa [Dsub] using hPrev
  have hStartEq :
      R.anchor + (D.terminal.value - r) =
        R.anchor + t.1 := by
    rw [hindex]
  have hDepthEq :
      Dsub.depth = Dt.depth := by
    exact
      windowDifference_depth_unique_of_start_eq
        hStartEq
        Dsub
        Dt
  have hCurrent :
      Dt.depth ≤
        (r + 1) * D.fixedPrefixExponentBound := by
    calc
      Dt.depth = Dsub.depth := hDepthEq.symm
      _ ≤
          (r + 1) * D.fixedPrefixExponentBound := hPrev'
  have hfactor :
      r + 1 ≤ D.terminal.value + 1 := by
    omega
  have hmul :
      (r + 1) * D.fixedPrefixExponentBound ≤
        (D.terminal.value + 1) *
          D.fixedPrefixExponentBound := by
    exact
      Nat.mul_le_mul_right
        D.fixedPrefixExponentBound
        hfactor
  unfold normalizationDepth normalizationDepthBound
  have hCurrent' :
      ((R.normalization (D.selectedIndex n)).difference
        t.1
        (by
          rw [D.selectedNormalization_terminalTime_eq n]
          exact Nat.le_of_lt_succ t.2)).depth ≤
        (r + 1) * D.fixedPrefixExponentBound := by
    simpa [Dt] using hCurrent
  exact le_trans hCurrent' hmul

/-- n番目のdepth patternを有限型へ符号化。 -/
noncomputable def depthPattern
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Fin (D.terminal.value + 1) → Fin (D.normalizationDepthBound + 1) :=
  fun t =>
    ⟨D.normalizationDepth n t,
      Nat.lt_succ_of_le (D.normalizationDepth_le_bound n t)⟩

/-- carry pattern固定後にdepth patternも固定した無限部分列。 -/
structure ConstantTerminalFixedDepthPatternData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  pattern :
    Fin (F.nested.terminal.value + 1) →
      Fin (F.nested.normalizationDepthBound + 1)
  pattern_eq : ∀ n : ℕ,
    F.nested.depthPattern (select n) = pattern

/-- `fixedDepthPatternSubsequence`: carry固定部分列からdepth pattern固定部分列を抽出。 -/
theorem fixedDepthPatternSubsequence
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D) :
    Nonempty (ConstantTerminalFixedDepthPatternData F) := by
  classical
  obtain ⟨P, hP⟩ :=
    cofinally_constant_of_finite F.nested.depthPattern
  let select : ℕ → ℕ :=
    Cofinally.select (fun n => F.nested.depthPattern n = P) hP
  exact ⟨{
    select := select
    select_strict :=
      Cofinally.select_strict (fun n => F.nested.depthPattern n = P) hP
    pattern := P
    pattern_eq := fun n =>
      Cofinally.select_spec (fun n => F.nested.depthPattern n = P) hP n
  }⟩

namespace ConstantTerminalFixedDepthPatternData

/-- depth固定後もConstant nested構造を保つ。 -/
def nested
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    {F : ConstantTerminalFixedCarryPatternData D}
    (P : ConstantTerminalFixedDepthPatternData F) :
    ConstantTerminalNestedAlignmentData R :=
  F.nested.refine P.select P.select_strict

end ConstantTerminalFixedDepthPatternData

end ConstantTerminalNestedAlignmentData
end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
