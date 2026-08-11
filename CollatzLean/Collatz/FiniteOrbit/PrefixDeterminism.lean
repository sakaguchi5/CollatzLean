import CollatzLean.Collatz.FiniteOrbit.Determinism

/-!
# actual run の prefix 決定性

同じ odd start から始まる actual run は、短い方の長さまでは同じ exponent word を走る。
full-length determinism の prefix 版。
-/

namespace Collatz
namespace Word
namespace Runs

/--
同じ start から始まる actual run で `v` の方が短ければ、
`v` は `u` の同じ長さの prefix。
-/
theorem word_eq_take_of_same_start_length_le
    {u v : Collatz.Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v x z)
    (hlen : v.length ≤ u.length) :
    v = u.take v.length := by
  induction hv generalizing u y with
  | nil x =>
      simp
  | @cons f v x z₁ z hf hstepF hz₁ htailV ih =>
      cases hu with
      | nil =>
          simp at hlen
      | @cons e u _ y₁ y he hstepE hy₁ htailU =>
          have hhead :=
            oneStep_unique hstepF hz₁ hstepE hy₁
          rcases hhead with ⟨hfe, hzy⟩
          subst e
          subst y₁
          have htailLen : v.length ≤ u.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
          have htailEq := ih htailU htailLen
          change
            f :: v =
              List.take (v.length + 1) (f :: u)
          calc
            f :: v
                = f :: List.take v.length u := by
                    rw [← htailEq]
            _ = List.take (v.length + 1) (f :: u) := by
                  rw [List.take_succ_cons]

end Runs
end Word
end Collatz
