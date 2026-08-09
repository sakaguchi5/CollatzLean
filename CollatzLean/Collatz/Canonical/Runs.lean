import CollatzLean.Collatz.Canonical.Residue
import CollatzLean.Collatz.FiniteOrbit.Runs

/-!
# actual runとcanonical start
-/

namespace Collatz
namespace Word
namespace Runs

/-- 非空actual runの開始値はcanonical剰余類に属する。 -/
theorem start_has_canonical_class
    {e : ℕ} {w : Collatz.Word} {x z : ℕ}
    (h : Runs (e :: w) x z) :
    ((x : ℕ) : ZMod (residueModulus (e :: w))) =
      canonicalClass (e :: w) := by
  exact Realizes.start_has_canonical_class h.realizes h.end_odd

/-- canonical modulusより小さいactual startはcanonicalStartそのもの。 -/
theorem start_eq_canonical_of_lt_modulus
    {e : ℕ} {w : Collatz.Word} {x z : ℕ}
    (h : Runs (e :: w) x z)
    (hx : x < residueModulus (e :: w)) :
    x = canonicalStart (e :: w) := by
  exact Realizes.eq_canonicalStart_of_lt_modulus
    h.realizes h.end_odd hx

end Runs
end Word
end Collatz
