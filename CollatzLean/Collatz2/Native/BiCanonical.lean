import CollatzLean.Collatz2.Native.IntervalReplay

/-!
# Collatz2 Native: thin bi-canonical property

`BiCanonical` を新しい trajectory data として bundle しない。
隣接二 word の replay quotient がともに0であるという Prop に薄くする。

従って bi-canonicality は既存 `ReplayCoordinate` の二つの zero-layer 条件にすぎない。
-/

namespace Collatz2
namespace Word

/--
隣接 realization `x -> y -> z` が両側で canonical replay layer `q=0` にある。
-/
def BiCanonicalAt
    (u v : Word)
    (x y z : ℕ) : Prop :=
  ∃ Cu : ReplayCoordinate u x y,
    Cu.quotient = 0 ∧
      ∃ Cv : ReplayCoordinate v y z,
        Cv.quotient = 0

/--
bi-canonicality は4つの canonical boundary equality と exact に同値。
特別な Data を保持する必要はない。
-/
theorem biCanonicalAt_iff_boundaries
    {u v : Word} {x y z : ℕ} :
    BiCanonicalAt u v x y z ↔
      x = canonicalStart u ∧
      y = canonicalEnd u ∧
      y = canonicalStart v ∧
      z = canonicalEnd v := by
  constructor
  · rintro ⟨Cu, hCu, Cv, hCv⟩
    exact
      ⟨Cu.start_eq_canonical_of_quotient_eq_zero hCu,
        Cu.finish_eq_canonical_of_quotient_eq_zero hCu,
        Cv.start_eq_canonical_of_quotient_eq_zero hCv,
        Cv.finish_eq_canonical_of_quotient_eq_zero hCv⟩
  · rintro ⟨hx, hyu, hyv, hz⟩
    let Cu : ReplayCoordinate u x y :=
      { quotient := 0
        start_eq := by simp only [hx, mul_zero, add_zero]
        finish_eq := by simp only [hyu, mul_zero, add_zero] }
    let Cv : ReplayCoordinate v y z :=
      { quotient := 0
        start_eq := by simp only [hyv, mul_zero, add_zero]
        finish_eq := by simp only [hz, mul_zero, add_zero] }
    exact ⟨Cu, rfl, Cv, rfl⟩

/--
隣接する二つの nonempty actual run で、両 start が canonical なら bi-canonical。
endpoint canonicality は replay coordinate の `q=0` から自動的に従う。
-/
theorem biCanonicalAt_of_runs_of_canonical_starts
    {u v : Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z)
    (hune : u ≠ [])
    (hvne : v ≠ [])
    (hx : x = canonicalStart u)
    (hy : y = canonicalStart v) :
    BiCanonicalAt u v x y z := by
  let Cu : ReplayCoordinate u x y := ReplayCoordinate.ofRuns hu hune
  let Cv : ReplayCoordinate v y z := ReplayCoordinate.ofRuns hv hvne
  have hCu : Cu.quotient = 0 :=
    Cu.quotient_eq_zero_of_start_eq_canonical hx
  have hCv : Cv.quotient = 0 :=
    Cv.quotient_eq_zero_of_start_eq_canonical hy
  exact ⟨Cu, hCu, Cv, hCv⟩

end Word

namespace Interval.Split

/-- `Interval.Split` 上での bi-canonicality は中央二 body の薄い property。 -/
def BiCanonicalAt
    {w : Word}
    (S : Interval.Split w)
    (x y z : ℕ) : Prop :=
  Word.BiCanonicalAt S.first S.second x y z

end Interval.Split
end Collatz2
