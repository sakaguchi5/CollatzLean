import CollatzLean.Collatz3.CSTMicro.CSTCriterion
import CollatzLean.Collatz3.CSTMicro.CriticalExpansion
import CollatzLean.Collatz3.CSTMicro.Realization
import CollatzLean.Collatz3.Semantics.FirstPassage
import CollatzLean.Collatz3.Bridge.RunsToCanonical


/-!
# Collatz3 CSTConditional: global CST assumption

このフォルダでは CST を未証明の **外部仮定** としてだけ使う。
既存の unconditional 本体へ仮定を混ぜないため、条件付き結果を独立 package に隔離する。

primitive assumption は一つだけ。

`GlobalCST := ∀ P : FirstPassagePath, P.CSTHolds`

`CSTHolds` 自体は既存 `CSTMicro` の定義であり、
一つの first coefficient crossing path の全 exact realization が strict descent することを表す。

このファイルでは、valid critical exponent word の actual run に対して
`GlobalCST` が strict descent を与えることだけを derived theorem として切り出す。
-/

namespace Collatz3
namespace CSTConditional

/--
すべての standard first coefficient crossing path で CST が成立する、という global 仮定。

この proposition 以外に新しい CST notion は導入しない。
-/
def GlobalCST : Prop :=
  ∀ P : CSTMicro.FirstPassagePath, P.CSTHolds

namespace GlobalCST

/-- global CST は任意の既存 first-passage path へ specialize できる。 -/
theorem path
    (G : GlobalCST)
    (P : CSTMicro.FirstPassagePath) :
    P.CSTHolds :=
  G P

/--
valid critical exponent word の whole affine realization は global CST により strict descent。

`CriticalFirstPassage` を standard parity path へ展開し、
既存 affine-equation ↔ exact-trace bridge を使う。
-/
theorem criticalEndpointEquation_descends
    (G : GlobalCST)
    {w : Word}
    {x y : ℕ}
    (hValid : Word.Valid w)
    (hFirst : Word.CriticalFirstPassage w)
    (hEq : w.EndpointEquation x y) :
    y < x := by
  let P : CSTMicro.FirstPassagePath :=
    CSTMicro.firstPassagePathOfCritical w hValid hFirst
  have hAffine :
      CSTMicro.AffineRealizes (CSTMicro.expandWord w) x y :=
    (CSTMicro.affineRealizes_expandWord_iff_wordEndpointEquation
      hValid x y).2 hEq
  have hTrace :
      CSTMicro.TraceRealizes (CSTMicro.expandWord w) x y :=
    hAffine.trace
  have hTraceP : CSTMicro.TraceRealizes P.word x y := by
    simpa [P] using hTrace
  exact (G.path P) x y hTraceP

/-- valid critical exponent word の actual run は global CST により strict descent。 -/
theorem criticalRun_descends
    (G : GlobalCST)
    {w : Word}
    {x y : ℕ}
    (hRun : Runs w x y)
    (hFirst : Word.CriticalFirstPassage w) :
    y < x := by
  exact
    G.criticalEndpointEquation_descends
      hRun.valid hFirst hRun.endpointEquation

/-- `ActualFirstPassage` は global CST の下で必ず strict descent。 -/
theorem actualFirstPassage_descends
    (G : GlobalCST)
    {w : Word}
    {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    y < x := by
  exact G.criticalRun_descends h.run h.critical

end GlobalCST
end CSTConditional
end Collatz3
