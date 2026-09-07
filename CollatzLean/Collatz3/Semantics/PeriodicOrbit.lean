import CollatzLean.Collatz3.Semantics.OrbitReturn

/-!
# Collatz3: actual periodic orbit の語彙

word / Hensel state の反復とは区別し、actual orbit の primitive return のみを
周期軌道と呼ぶ。開始点 `1` の primitive return を自明周期、それ以外を
非自明周期として分離する。
-/

namespace Collatz3

/-- `1` を基点とする actual primitive periodic orbit。 -/
def IsTrivialPeriodicOrbit (w : Word) (x : ℕ) : Prop :=
  PrimitiveReturn w x ∧ x = 1

/-- `1` 以外を基点とする actual primitive periodic orbit。 -/
def IsNontrivialPeriodicOrbit (w : Word) (x : ℕ) : Prop :=
  PrimitiveReturn w x ∧ x ≠ 1

namespace PrimitiveReturn

/-- primitive return は自明周期か非自明周期のどちらか。 -/
theorem trivial_or_nontrivial
    {w : Word} {x : ℕ}
    (h : PrimitiveReturn w x) :
    IsTrivialPeriodicOrbit w x ∨ IsNontrivialPeriodicOrbit w x := by
  by_cases hx : x = 1
  · exact Or.inl ⟨h, hx⟩
  · exact Or.inr ⟨h, hx⟩

end PrimitiveReturn

/-- 自明周期と非自明周期は同時には成立しない。 -/
theorem trivialPeriodicOrbit_disjoint_nontrivial
    {w : Word} {x : ℕ}
    (hTrivial : IsTrivialPeriodicOrbit w x)
    (hNontrivial : IsNontrivialPeriodicOrbit w x) :
    False :=
  hNontrivial.2 hTrivial.2

end Collatz3
