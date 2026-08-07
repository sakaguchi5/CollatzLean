import CollatzLean.CollatzSecondLayer3.FutureMinimumTerminalDichotomy

/-!
# future-minimumから全正長を同時に扱うfirst-deferred系

従来はSpecial C3部分列やdeep lower-replay部分列を先に抽出していた。
このファイルでは固定future-minimum anchorから、全ての正長`q + 1`について
first-deferred normalizationを直接保持する。

Constant terminal排除後の主証明では、部分列のterminal geometryを経由せず、
この全長さ系のterminal timeが固定有限時刻から逃げることを直接示す。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer

/--
非有界odd-only軌道上の一つのfuture-minimum anchorから、
全ての正長`q + 1`のfirst-deferred normalizationを生成するための正本データ。
-/
structure FutureMinimumAllLengthTerminalData (O : OddOrbit) where
  unbounded : O.Unbounded
  anchor : ℕ
  futureMinimum : O.FutureMinimumAt anchor

namespace FutureMinimumAllLengthTerminalData

/-- `q`番目に扱うwindow長。全正長をちょうど一度ずつ列挙する。 -/
def length
    {O : OddOrbit}
    (_A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) : ℕ :=
  q + 1

/-- 全長さ系のwindow長は正。 -/
theorem length_pos
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) :
    0 < A.length q := by
  unfold length
  omega

/-- `q + 1` windowのfirst-deferred normalization。 -/
noncomputable def normalization
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) :
    O.FiniteCaptureNormalizationData
      (futureMinimumWindowDifference
        O A.unbounded A.anchor (A.length q)
        A.futureMinimum (A.length_pos q)) :=
  futureMinimumFirstDeferredData
    O A.unbounded A.anchor (A.length q)
    A.futureMinimum (A.length_pos q)

/-- `q + 1` windowのfirst-deferred terminal time。 -/
noncomputable def terminalTime
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) : ℕ :=
  (A.normalization q).terminalTime

/-- `q + 1` windowのfirst-deferred terminal開始位置。 -/
noncomputable def terminalStart
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) : ℕ :=
  A.anchor + A.terminalTime q

/-- 全長さ系のterminalはdeferred。 -/
noncomputable def terminal_deferred
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) :
    O.DeferredWindowAt (A.terminalStart q) (A.length q) := by
  simpa [terminalStart, terminalTime] using
    (A.normalization q).terminal

/-- terminal以前ではcaptureまたはsynchronizedのどちらか。 -/
theorem before
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q t : ℕ)
    (ht : t < A.terminalTime q) :
    Nonempty
      (O.CapturedWindowAt
          (A.anchor + t) (A.length q) ⊕
       O.SynchronizedWindowAt
          (A.anchor + t) (A.length q)) := by
  simpa [terminalTime] using
    (A.normalization q).before t ht

/-- `q + 1` terminalがSpecial C3であるという局所predicate。 -/
def IsSpecial
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) : Prop :=
  Nonempty (SpecialC3At O (A.terminalStart q) (A.length q))

/-- `q + 1` terminalがdeep lower replayであるという局所predicate。 -/
def IsDeep
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) : Prop :=
  Nonempty (GenericDeepLowerReplayAt O (A.terminalStart q) (A.length q))

/--
全ての長さでterminalはdeep lower replayまたはSpecial C3のどちらかへ落ちる。
この局所二分岐だけを、Constant terminal抽出に使用する。
-/
theorem terminal_deep_or_special
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (q : ℕ) :
    A.IsDeep q ∨ A.IsSpecial q := by
  exact
    deferredWindow_generic_dichotomy
      (A.terminal_deferred q)
      (A.length_pos q)

/--
非有界odd-only軌道から標準future-minimumを一つ選び、
全長さfirst-deferred系を直接構成する。
-/
noncomputable def ofUnbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    FutureMinimumAllLengthTerminalData O := by
  let anchor : ℕ := O.tailMinIndex 0
  have hmin : O.FutureMinimumAt anchor := by
    simpa [anchor] using O.futureMinimumAt_tailMinIndex 0
  exact
    { unbounded := hU
      anchor := anchor
      futureMinimum := hmin }

end FutureMinimumAllLengthTerminalData
end CollatzSecondLayer3
