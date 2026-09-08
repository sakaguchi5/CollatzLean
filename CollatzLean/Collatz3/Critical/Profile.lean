import CollatzLean.Collatz3.Critical.Beatty

/-!
# Collatz3: thin critical profile

profile は relevant column だけを持つ有限関数 `Fin m → ℕ`。
checkpoint は Beatty roof から profile depth を引いて導く。
-/

namespace Collatz3
namespace Critical

/-- `m` 個の critical columns に対する有限 depth profile。 -/
abbrev Profile (m : ℕ) := Fin m → ℕ

/-- profile column `k` の checkpoint。 -/
def checkpoint
    {m : ℕ}
    (h : Profile m)
    (k : Fin m) : ℕ :=
  beattyIndex k.1 - h k

/-- Beatty roof 以下かつ adjacent checkpoint が strict に増加する。 -/
def Admissible
    {m : ℕ}
    (h : Profile m) : Prop :=
  (∀ k : Fin m, h k ≤ beattyIndex k.1) ∧
  (∀ k : ℕ, (hk : k + 1 < m) →
    checkpoint h ⟨k, by omega⟩ <
      checkpoint h ⟨k + 1, hk⟩)

namespace Admissible

/-- admissible profile は各 column で Beatty roof 以下。 -/
theorem depth_le
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (k : Fin m) :
    h k ≤ beattyIndex k.1 :=
  A.1 k

/-- adjacent checkpoint は strict。 -/
theorem checkpoint_strict
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {k : ℕ}
    (hk : k + 1 < m) :
    checkpoint h ⟨k, by omega⟩ <
      checkpoint h ⟨k + 1, hk⟩ :=
  A.2 k hk

/-- `m>0` の admissible profile では最初の depth は 0。 -/
theorem first_depth_eq_zero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    h ⟨0, hm⟩ = 0 := by
  have hLe := A.depth_le ⟨0, hm⟩
  simp only [beattyIndex_zero, nonpos_iff_eq_zero] at hLe
  exact hLe

/-- `m>0` の admissible profile では最初の checkpoint は 0。 -/
theorem first_checkpoint_eq_zero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    checkpoint h ⟨0, hm⟩ = 0 := by
  simp [checkpoint, A.first_depth_eq_zero hm]

end Admissible

end Critical
end Collatz3
