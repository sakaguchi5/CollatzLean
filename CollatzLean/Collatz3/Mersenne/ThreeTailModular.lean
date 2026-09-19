import CollatzLean.Collatz3.Mersenne.TailLoopModular
import Std.Data.HashSet.Lemmas
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: shared 3-adic tail modulus

one-hole large-depth sieve で使ってきた

`M₄ = 3^6 * 7 * 19 * 73 * 163 * 487 = 561847684041`

の tail/loop certificate だけを、finite sieve 本体から独立させる。

今後 source-two resonance など別 branch が M₄ を使う際、
`OneHoleFiniteTailLoopSieve` や `OneHoleFiniteLift65536` を import する必要はない。
既存 one-hole theorem 名との衝突を避けるため `ThreeTail` namespace に置く。
-/

namespace Collatz3
namespace Mersenne
namespace ThreeTail

/-- 共通 3-adic tail modulus `M₄`。 -/
def modulus : ℕ := 561847684041

/-- `M₄` 上で 2 は tail 0、period 486。 -/
theorem twoLoop :
    PowTailLoop modulus 2 0 486 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- `M₄` 上で 3 は tail 6、その後 period 972。 -/
theorem threeLoop :
    PowTailLoop modulus 3 6 972 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- 2/3 を同時に使う shared certificate。 -/
theorem loops :
    Pow23TailLoops modulus 0 486 6 972 :=
  ⟨twoLoop, threeLoop⟩

/-- `k≥6` の 3-tail representative。 -/
def largeDepthKRep (j : Fin 972) : ℕ :=
  6 + j.1

/-- 2-exponent は単純に `mod 486` へ落ちる。 -/
theorem reduceTwoExponent (e : ℕ) :
    tailLoopExponent 0 486 e = e % 486 := by
  simp [tailLoopExponent]

/-- `k≥6` では 3-exponent は `6 + ((k-6) mod 972)` へ落ちる。 -/
theorem reduceThreeExponent_of_largeDepth
    {k : ℕ}
    (hk : 6 ≤ k) :
    tailLoopExponent 6 972 k = 6 + ((k - 6) % 972) := by
  simp [tailLoopExponent, show ¬ k < 6 by omega]

end ThreeTail
end Mersenne
end Collatz3
