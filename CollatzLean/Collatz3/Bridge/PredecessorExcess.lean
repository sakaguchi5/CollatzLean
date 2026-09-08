import CollatzLean.Collatz3.FixedFiber.PrependExcess
import CollatzLean.Collatz3.Semantics.Predecessor

/-!
# Collatz3: actual predecessor と fixed-fiber excess の橋

pure fixed-fiber arithmetic と actual inverse Collatz semantics をここで初めて接続する。

`FixedFiber.PrependExcess` 自体は `Runs` / `BackwardStep` を import しない。
逆向き枝

`e ↦ e+2`

に対して、

`x ↦ 4*x+1`

と

`signed centered E_RF ↦ 4 * signed centered E_RF`

が同じ操作から同時に従うことを bridge theorem として置く。
-/

namespace Collatz3
namespace Word

/--
実際の逆向き 1 step と同じ tail run を固定した signed 4 倍相似。

`x --e--> y` を逆向きに読んでいるとき、
指数を `e+2` にした枝は `4*x+1` から同じ `y` へ入る。
tail `w` をそのまま続けると同じ終点 `z` へ到達し、
signed 中心化 `E_RF` 座標も exact に 4 倍される。
-/
theorem backwardBranch_add_two_signed_four_similarity
    {e x y z : ℕ}
    {w : Word}
    (hStep : BackwardStep e y x)
    (hTail : Runs w y z) :
    BackwardStep (e + 2) y (4 * x + 1) ∧
      Runs ((e + 2) :: w) (4 * x + 1) z ∧
      signedPrependExcessCoordinate (e + 2) w =
        4 * signedPrependExcessCoordinate e w := by
  have hNext : BackwardStep (e + 2) y (4 * x + 1) :=
    BackwardStep.add_two hStep
  refine ⟨hNext, Runs.cons hNext hTail, ?_⟩
  exact signedPrependExcessCoordinate_add_two e w

/--
従来互換の Nat-valued 4 倍相似。

full theorem の正本は signed 版。
actual tail から得る validity と `e>0` によって Nat view へ戻す。
-/
theorem backwardBranch_add_two_four_similarity
    {e x y z : ℕ}
    {w : Word}
    (hStep : BackwardStep e y x)
    (hTail : Runs w y z) :
    BackwardStep (e + 2) y (4 * x + 1) ∧
      Runs ((e + 2) :: w) (4 * x + 1) z ∧
      prependExcessCoordinate (e + 2) w =
        4 * prependExcessCoordinate e w := by
  have hSigned :=
    backwardBranch_add_two_signed_four_similarity
      (hStep := hStep) (hTail := hTail)
  have hValid : Valid w := Runs.valid hTail
  have he : 0 < e := BackwardStep.exponent_pos hStep
  refine ⟨hSigned.1, hSigned.2.1, ?_⟩
  exact prependExcessCoordinate_add_two he hValid

end Word
end Collatz3
