import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 第3例探索 7: Ostrowski / Record 標準ブロック転送の合成核

65 億個の局所 step を保持せず、標準ブロックごとに

  x ↦ a x + b

という affine transfer だけを memoize する。

ブロック連結は transfer の関数合成そのものなので、DAG 上では
この小さい summary だけを再利用すればよい。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 標準ブロックが整数状態へ作用する affine summary。 -/
@[ext]
structure StandardBlockTransfer where
  mul : ℤ
  add : ℤ
  deriving DecidableEq

/-- transfer の作用。 -/
def StandardBlockTransfer.apply
    (T : StandardBlockTransfer) (x : ℤ) : ℤ :=
  T.mul * x + T.add

/-- `before` を適用した後に `after` を適用する合成。 -/
def StandardBlockTransfer.comp
    (after before : StandardBlockTransfer) : StandardBlockTransfer :=
  {
    mul := after.mul * before.mul
    add := after.mul * before.add + after.add
  }

/-- 空ブロックに対応する恒等 transfer。 -/
def StandardBlockTransfer.id : StandardBlockTransfer :=
  { mul := 1, add := 0 }

/--
標準ブロックの summary 合成は、実際の状態への作用の関数合成と exact に一致する。
-/
theorem standardBlockTransfer_comp
    (after before : StandardBlockTransfer)
    (x : ℤ) :
    (after.comp before).apply x =
      after.apply (before.apply x) := by
  simp [StandardBlockTransfer.comp, StandardBlockTransfer.apply]
  ring

/-- 恒等ブロックを左から合成しても変わらない。 -/
theorem StandardBlockTransfer.id_comp
    (T : StandardBlockTransfer) :
    StandardBlockTransfer.id.comp T = T := by
  cases T
  simp [StandardBlockTransfer.id, StandardBlockTransfer.comp]

/-- 恒等ブロックを右から合成しても変わらない。 -/
theorem StandardBlockTransfer.comp_id
    (T : StandardBlockTransfer) :
    T.comp StandardBlockTransfer.id = T := by
  cases T
  simp [StandardBlockTransfer.id, StandardBlockTransfer.comp]

/-- summary の合成は結合的であり、標準ブロック DAG の括り方に依存しない。 -/
theorem StandardBlockTransfer.comp_assoc
    (A B C : StandardBlockTransfer) :
    A.comp (B.comp C) = (A.comp B).comp C := by
  apply StandardBlockTransfer.ext <;>
    simp [StandardBlockTransfer.comp] <;> ring

end ThirdExampleSearch
end CSTMicro
end Collatz2
