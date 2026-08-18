import CollatzLean.Collatz2.CSTMicro.CarryGeometry.CriticalBoundaryExtraDepth

/-!
# Ferrers column occupancy = extra-depth

`ExtraDepthFerrersTransport` で一つの Ferrers step は selected rank column だけを +1 する。
そこで chain が各 rank cut `k` を何回通過したかを `rankColumnOccupancy` として数える。

  extraDepth(finish,k)
    = extraDepth(start,k) + occupancy(chain,k)

が exact に telescope する。
critical Sturmian boundary は `extraDepth=0` なので、そこから始まる chain では

  extraDepth(finish,k) = occupancy(chain,k)

となる。これにより `extraDepth` は Ferrers diagram の pure column height そのものになる。
-/

namespace Collatz2
namespace CSTMicro

namespace FerrersChain

/-- chain が rank cut `k` の Ferrers cell を何回通過したか。 -/
def rankColumnOccupancy
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ → ℕ
  | .refl _, _ => 0
  | .step C S, k =>
      C.rankColumnOccupancy k + if k = S.edge.rankCut then 1 else 0

@[simp] theorem rankColumnOccupancy_refl
    (v : ParityWord)
    (k : ℕ) :
    (FerrersChain.refl v).rankColumnOccupancy k = 0 := by
  rfl

@[simp] theorem rankColumnOccupancy_step
    {start mid finish : ParityWord}
    (C : FerrersChain start mid)
    (S : FerrersStep mid finish)
    (k : ℕ) :
    (FerrersChain.step C S).rankColumnOccupancy k =
      C.rankColumnOccupancy k + if k = S.edge.rankCut then 1 else 0 := by
  rfl

/--
extra-depth profile は column occupancy を exact に積分する。
-/
theorem parityExtraDepth_eq_start_add_rankColumnOccupancy
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hStartLen : 1 < start.length)
    (k : ℕ) :
    parityExtraDepth finish k =
      parityExtraDepth start k + C.rankColumnOccupancy k := by
  induction C with
  | refl =>
      simp [rankColumnOccupancy]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hULen : 1 < u.length := by
        rw [← C.length_eq]
        exact hStartLen
      have hStep := S.parityExtraDepth_step hUFP k
      change
        parityExtraDepth v k =
          parityExtraDepth start k +
            (C.rankColumnOccupancy k +
              if k = S.edge.rankCut then 1 else 0)
      rw [hStep, ih]
      omega

/-- chain endpoints の odd-only cut count は同じ。 -/
theorem exponentOddSteps_eq
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    Collatz2.Word.oddSteps (exponentWordOfParity start) =
      Collatz2.Word.oddSteps (exponentWordOfParity finish) := by
  rw [oddSteps_exponentWordOfParity, oddSteps_exponentWordOfParity]
  exact C.oddCount_eq

end FerrersChain

/--
critical boundary 起点では final extra-depth は pure column occupancy そのもの。
-/
theorem criticalBoundary_to_finish_extraDepth_eq_columnOccupancy
    {v finish : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    {k : ℕ}
    (hkLt :
      k < Collatz2.Word.oddSteps
        (exponentWordOfParity (criticalBoundaryWord v.length))) :
    parityExtraDepth finish k = C.rankColumnOccupancy k := by
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord v.length) :=
    criticalBoundaryWord_isFirstPassage hFP
  have hBoundaryLen : 1 < (criticalBoundaryWord v.length).length := by
    simpa using hLen
  have hTel :=
    C.parityExtraDepth_eq_start_add_rankColumnOccupancy
      hBoundaryFP hBoundaryLen k
  have hZero :=
    criticalBoundaryWord_parityExtraDepth_eq_zero hFP hLen hkLt
  rw [hZero, Nat.zero_add] at hTel
  exact hTel

/--
pointwise pure-object packet: final depth profile と chain occupancy profile は一致する。
-/
structure FerrersColumnOccupancyPacket
    (boundary finish : ParityWord) where
  chain : FerrersChain boundary finish
  boundaryFirstPassage : IsFirstPassageWord boundary
  boundaryLength : 1 < boundary.length
  boundaryZeroDepth :
    ∀ k : ℕ,
      k < Collatz2.Word.oddSteps (exponentWordOfParity boundary) →
      parityExtraDepth boundary k = 0

namespace FerrersColumnOccupancyPacket

/-- packet の final proper-cut depth は occupancy。 -/
theorem finish_extraDepth_eq_occupancy
    {boundary finish : ParityWord}
    (P : FerrersColumnOccupancyPacket boundary finish)
    {k : ℕ}
    (hkLt : k < Collatz2.Word.oddSteps (exponentWordOfParity boundary)) :
    parityExtraDepth finish k = P.chain.rankColumnOccupancy k := by
  have hTel :=
    P.chain.parityExtraDepth_eq_start_add_rankColumnOccupancy
      P.boundaryFirstPassage P.boundaryLength k
  rw [P.boundaryZeroDepth k hkLt, Nat.zero_add] at hTel
  exact hTel

end FerrersColumnOccupancyPacket

end CSTMicro
end Collatz2
