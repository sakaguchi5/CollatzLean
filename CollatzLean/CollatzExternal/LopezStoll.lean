import CollatzLean.CollatzOrbitCore.InfiniteOrbit
import CollatzLean.CollatzFirstLayer.Basic

/-!
# López–Stoll臨界密度のodd-only入力境界

実数極限を上位層へ漏らさず、`3^n / 2^H = 2^o(n)`の上側だけを
自然数冪の不等式として受け取る。
-/

namespace CollatzExternal

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- anchor `a`からの累積指数が臨界密度の上側を満たす。
`m`を大きくするほど許される線形誤差`n/m`が小さくなる。 -/
def CriticalExponentDensityAt (O : OddOrbit) (a : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (3 ^ n) ^ m ≤
        2 ^ (m * twoSteps (O.segmentWord a n) + n)

/-- 非有界自然数odd-only軌道の全tailに対するLópez–Stoll入力。 -/
def LopezStollCriticalDensityPrinciple : Prop :=
  ∀ O : OddOrbit, O.Unbounded →
    ∀ a : ℕ, CriticalExponentDensityAt O a

end CollatzExternal
