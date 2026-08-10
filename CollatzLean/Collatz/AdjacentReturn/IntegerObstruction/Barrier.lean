import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Chain
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Expanding
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Contracting
import CollatzLean.Collatz.FiniteOrbit.Runs

/-!
# backward barrier refinement

有限範囲の計算検証など、純 Collatz 算術とは独立な外部入力から得る
「反例 basin はある下限 B より下へ入れない」という制約を、
共通 AdjacentIntegerChain 上の refinement として分離する。

このファイル自体は具体的な検証境界を公理化しない。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/--
連続 adjacent integer chain に対する reverse barrier。

`reverse_ge` は chain start へ actual finite odd run で入る任意の祖先が
`bound` 以上であることを要求する。
-/
structure ReverseBarrier (bound : ℕ) (C : AdjacentIntegerChain) : Prop where
  bound_pos : 0 < bound
  start_ge :
    ∀ n : ℕ, bound ≤ (C.block n).startValue
  reverse_ge :
    ∀ n : ℕ,
    ∀ w : Collatz.Word,
    ∀ z : ℕ,
      Word.Runs w z (C.block n).startValue →
        bound ≤ z

namespace ReverseBarrier

/-- adjacent endpoint も次 block の start なので barrier 以上。 -/
theorem next_ge
    {bound : ℕ} {C : AdjacentIntegerChain}
    (R : ReverseBarrier bound C) (n : ℕ) :
    bound ≤ (C.block n).startValue + (C.block n).valueGap := by
  rw [C.connects n]
  exact R.start_ge (n + 1)

/-- chain の値は全て正の barrier の上にある。 -/
theorem start_pos
    {bound : ℕ} {C : AdjacentIntegerChain}
    (R : ReverseBarrier bound C) (n : ℕ) :
    0 < (C.block n).startValue :=
  lt_of_lt_of_le R.bound_pos (R.start_ge n)

end ReverseBarrier

/-- expanding obstruction に backward barrier を積んだ refinement。 -/
structure BarrierExpandingIntegerTower (bound : ℕ) where
  core : ExpandingIntegerTower
  barrier : ReverseBarrier bound core.chain

/-- contracting obstruction に backward barrier を積んだ refinement。 -/
structure BarrierContractingIntegerChain (bound : ℕ) where
  core : ContractingIntegerChain
  barrier : ReverseBarrier bound core.chain

/-- expanding barrier obstruction が存在すること。 -/
def HasBarrierExpandingIntegerTower (bound : ℕ) : Prop :=
  Nonempty (BarrierExpandingIntegerTower bound)

/-- contracting barrier obstruction が存在すること。 -/
def HasBarrierContractingIntegerChain (bound : ℕ) : Prop :=
  Nonempty (BarrierContractingIntegerChain bound)

end IntegerObstruction
end AdjacentReturn
end Collatz
