import CollatzLean.Collatz.OddOrbit.FutureMinimum

/-!
# 標準future-minimum列の隣接性

単なるfuture-minimum部分列と、current+1以後のtail minimumを毎回選ぶ標準列を
区別する。Adjacent Returnのsuffix geometryはこの情報を必要とする。
-/

namespace Collatz
namespace OddOrbit
namespace FutureMinima

/-- 次項がcurrentより後の任意の値以下であるという標準隣接性。 -/
def IsStandard {O : OddOrbit} (S : O.FutureMinima) : Prop :=
  ∀ j t : ℕ, S.index j < t → O.value (S.index (j + 1)) ≤ O.value t

end FutureMinima
end OddOrbit
end Collatz
