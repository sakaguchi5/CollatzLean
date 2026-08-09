import CollatzLean.Collatz.Canonical.CylinderDerived

/-!
# zero-cylinderとactual odd dynamics

一文字zero cylinderがcanonical endからの実際の次odd-stepと同値であること、
およびactual runの連結をまとめる。
-/

namespace Collatz
namespace Word

namespace Runs

/-- actual runどうしを端点で連結する。 -/
theorem append
    {u v : Collatz.Word} {x y z : ℕ}
    (h₁ : Runs u x y)
    (h₂ : Runs v y z) :
    Runs (u ++ v) x z := by
  induction h₁ generalizing z with
  | nil x =>
      simpa using h₂
  | @cons e w x y t he hstep hy htail ih =>
      simp only [List.cons_append]
      exact Runs.cons he hstep hy (ih h₂)

end Runs

/-- `e`が`x`からのactual odd-only次指数であること。 -/
def IsNextOddExponentAt (x e : ℕ) : Prop :=
  ∃ y : ℕ, Runs ([e] : Collatz.Word) x y

/--
一文字zero cylinderなら、旧canonical endからその指数`e`で
延長canonical endへ実際に一歩進む。
-/
theorem runs_singleton_from_canonicalEnd_of_extensionDigit_eq_zero
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ [])
    (hzero : u.extensionDigit [e] = 0) :
    Runs ([e] : Collatz.Word)
      u.canonicalEnd
      (u ++ [e]).canonicalEnd := by
  have hsplit :=
    canonicalRuns_append_split_at_boundary
      (u := u) (v := [e]) hvalid hu
  have hboundary :
      u.canonicalPrefixBoundary [e] = u.canonicalEnd :=
    (extensionDigit_zero_iff_boundary_canonical u [e]).1 hzero
  have hsuffix := hsplit.2
  rw [hboundary] at hsuffix
  simpa using hsuffix

/--
validな一文字延長では、zero cylinderであることと
`e`が旧canonical endにおけるactual next odd exponentであることは同値。
-/
theorem extensionDigit_singleton_eq_zero_iff_nextOddExponentAt_canonicalEnd
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    u.extensionDigit [e] = 0 ↔
      IsNextOddExponentAt u.canonicalEnd e := by
  constructor
  · intro hzero
    exact
      ⟨(u ++ [e]).canonicalEnd,
        runs_singleton_from_canonicalEnd_of_extensionDigit_eq_zero
          hvalid hu hzero⟩
  · intro hnext
    rcases hnext with ⟨y, hstep⟩
    have huvalid : u.Valid := hvalid.prefix
    have hurun : Runs u u.canonicalStart u.canonicalEnd :=
      huvalid.canonicalRuns
    have hreal :
        (u ++ [e]).Realizes u.canonicalStart y :=
      hurun.realizes.append hstep.realizes
    have hy : Odd y := hstep.end_odd
    have hmodulus :
        (u ++ [e]).residueModulus =
          u.residueModulus * 2 ^ e := by
      simp [residueModulus, pow_add, Nat.add_comm,
        Nat.add_left_comm, Nat.mul_comm]
    have hpowOne : 1 ≤ 2 ^ e := by
      have hpos : 0 < 2 ^ e := Nat.pow_pos (by omega)
      omega
    have hmodLe :
        u.residueModulus ≤ (u ++ [e]).residueModulus := by
      rw [hmodulus]
      have h := Nat.mul_le_mul_left u.residueModulus hpowOne
      simpa using h
    have hstartLt :
        u.canonicalStart < (u ++ [e]).residueModulus :=
      lt_of_lt_of_le (canonicalStart_lt_modulus u) hmodLe
    have hcanonical :
        u.canonicalStart = (u ++ [e]).canonicalStart :=
      hreal.eq_canonicalStart_of_lt_modulus hy hstartLt
    unfold extensionDigit
    rw [← hcanonical]
    exact Nat.div_eq_of_lt (canonicalStart_lt_modulus u)

end Word
end Collatz
