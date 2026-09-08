import CollatzLean.Collatz3.Critical.Profile
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz3: critical profile affine numerator

profile checkpoint から odd-only affine translation と同型の finite sum

  A(h) = Σ_{k<m} 2^(checkpoint_k) 3^(m-k-1)

を直接定義する。actual word との一致は Bridge 層で扱う。
-/

namespace Collatz3
namespace Critical

open scoped BigOperators

/-- profile column `k` の affine monomial。 -/
def profileAffineTerm
    {m : ℕ}
    (h : Profile m)
    (k : Fin m) : ℕ :=
  2 ^ checkpoint h k * 3 ^ (m - (k.1 + 1))

/-- profile checkpoint から作る affine numerator `A(h)`。 -/
def profileAffineNumerator
    {m : ℕ}
    (h : Profile m) : ℕ :=
  ∑ k : Fin m, profileAffineTerm h k

@[simp] theorem profileAffineNumerator_zero
    (h : Profile 0) :
    profileAffineNumerator h = 0 := by
  simp [profileAffineNumerator]

end Critical
end Collatz3
