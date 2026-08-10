import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Basic
import CollatzLean.Collatz.OddOrbit.Selection
import CollatzLean.Collatz.OddOrbit.StandardSelection
/-!
# 標準 adjacent return の連続整数 chain

標準 future-minimum 列の全 adjacent return を落とさず、
連続する純算術 block として保持する。

expanding / eventually-contracting はこの共通 chain 上の条件として扱う。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/--
標準 adjacent return の連続純算術 chain。

各 block の next value は次 block の start value に一致する。
-/
structure AdjacentIntegerChain where
  block : ℕ → BlockArithmeticData
  connects :
    ∀ n : ℕ,
      (block n).startValue + (block n).valueGap =
        (block (n + 1)).startValue

namespace AdjacentIntegerChain

/-- 連続した actual adjacent state 列から純算術 chain を作る。 -/
def ofStateSequence
    {O : OddOrbit}
    (state : ℕ → State O)
    (hnext : ∀ n : ℕ, (state n).nextValue = (state (n + 1)).startValue) :
    AdjacentIntegerChain := by
  refine {
    block := fun n => BlockArithmeticData.ofState (state n)
    connects := ?_
  }
  intro n
  change
    (state n).startValue + (state n).valueGap =
      (state (n + 1)).startValue
  rw [← (state n).nextValue_eq_startValue_add_valueGap]
  exact hnext n

/-- 同じ標準 future-minimum 列の index `j` と `j+1` は値で接続する。 -/
private theorem nextValue_eq_succ_startValue
    {O : OddOrbit}
    (hU : O.Unbounded)
    (minima : O.FutureMinima)
    (standard : minima.IsStandard)
    (j : ℕ) :
    (State.mk hU minima standard j).nextValue =
      (State.mk hU minima standard (j + 1)).startValue := by
  rfl

/-- 標準 future-minimum 列全体から連続純算術 chain を作る。 -/
def ofStandardFutureMinima
    {O : OddOrbit}
    (hU : O.Unbounded)
    (minima : O.FutureMinima)
    (standard : minima.IsStandard) :
    AdjacentIntegerChain :=
  ofStateSequence
    (fun n => State.mk hU minima standard n)
    (fun n => nextValue_eq_succ_startValue hU minima standard n)

/-- 標準 future-minimum 列の `offset` 以後から連続純算術 chain を作る。 -/
def ofStandardFutureMinimaFrom
    {O : OddOrbit}
    (hU : O.Unbounded)
    (minima : O.FutureMinima)
    (standard : minima.IsStandard)
    (offset : ℕ) :
    AdjacentIntegerChain :=
  ofStateSequence
    (fun n => State.mk hU minima standard (offset + n))
    (fun n => by
      simpa [Nat.add_assoc] using
        nextValue_eq_succ_startValue
          hU minima standard (offset + n))

/-- 非有界 odd 軌道から標準 adjacent return の連続純算術 chain を選ぶ。 -/
noncomputable def ofUnboundedOrbit
    (O : OddOrbit) (hU : O.Unbounded) :
    AdjacentIntegerChain := by
  classical
  let minima : O.FutureMinima :=
    OddOrbit.Selection.futureMinima O hU
  have standard : minima.IsStandard := by
    dsimp [minima]
    exact OddOrbit.Selection.futureMinima_isStandard O hU
  exact ofStandardFutureMinima hU minima standard

/-- 連続 chain の start value は一段ごとに真に増加する。 -/
theorem startValue_lt_succ
    (C : AdjacentIntegerChain) (n : ℕ) :
    (C.block n).startValue < (C.block (n + 1)).startValue := by
  have hgap := (C.block n).valueGap_pos
  rw [← C.connects n]
  omega

/-- 連続 chain の start value は狭義単調。 -/
theorem startValue_strict
    (C : AdjacentIntegerChain) :
    StrictMono (fun n => (C.block n).startValue) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact C.startValue_lt_succ n

end AdjacentIntegerChain
end IntegerObstruction
end AdjacentReturn
end Collatz
