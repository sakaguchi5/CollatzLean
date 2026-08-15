import CollatzLean.Collatz2.Geometry.CriticalCarry

/-!
# Collatz2 Geometry: minimal FirstCrossing blocks

record/Ferrers factorization の local atom。
一つの block は FirstCrossing であり、terminal two-depth が
`criticalHeight(length)+1` という最小 contracting depth にある。
-/

namespace Collatz2
namespace Word

/-- 最小 contracting depth を持つ FirstCrossing word。 -/
structure MinimalCrossingBlock (w : Word) : Prop where
  firstCrossing : FirstCrossing w
  minimalDepth :
    twoSteps w = criticalHeight (oddSteps w) + 1

/-- genuine Collatz exponent word として valid でもある minimal block。 -/
structure ValidMinimalCrossingBlock (w : Word) : Prop extends MinimalCrossingBlock w where
  valid : Valid w

namespace MinimalCrossingBlock

/-- minimal block は nonempty。 -/
theorem nonempty
    {w : Word}
    (M : MinimalCrossingBlock w) :
    w ≠ [] :=
  M.firstCrossing.nonempty

/-- minimal block の odd-step 数は正。 -/
theorem oddSteps_pos
    {w : Word}
    (M : MinimalCrossingBlock w) :
    0 < oddSteps w := by
  unfold oddSteps
  exact List.length_pos_iff.mpr M.nonempty

/-- minimal block terminal は contracting。 -/
theorem contracting
    {w : Word}
    (M : MinimalCrossingBlock w) :
    Contracting w :=
  M.firstCrossing.terminalContracting

end MinimalCrossingBlock

/-- 長さを外部 index として持つ minimal block。 -/
structure MinimalCrossingBlockOfLength (r : ℕ) where
  word : Word
  block : MinimalCrossingBlock word
  oddSteps_eq : oddSteps word = r

/-- valid 版。local translation spectrum はこちらを使う。 -/
structure ValidMinimalCrossingBlockOfLength (r : ℕ) where
  word : Word
  block : ValidMinimalCrossingBlock word
  oddSteps_eq : oddSteps word = r

namespace MinimalCrossingBlockOfLength

/-- 指定長 minimal block の total depth。 -/
theorem twoSteps_eq
    {r : ℕ}
    (M : MinimalCrossingBlockOfLength r) :
    twoSteps M.word = criticalHeight r + 1 := by
  rw [M.block.minimalDepth, M.oddSteps_eq]

end MinimalCrossingBlockOfLength

end Word
end Collatz2
