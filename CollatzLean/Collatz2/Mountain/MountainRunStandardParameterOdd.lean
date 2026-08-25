import CollatzLean.Collatz2.Mountain.Block

/-!
# MountainRun: standard parameter の odd 性

`MountainRun.exists_standard_parameter` が与える Hercher 型 parameter `a` について、
完全 mountain の drop が少なくとも一回の even step を含むことから `a` が odd であることを
同時に回収する。
-/

namespace Collatz2
namespace Word
namespace MountainRun

/--
actual mountain の standard parameter は odd に取れる。

既存 theorem

  x    = a * 2^k - 1
  peak = a * 3^k - 1
  2^l * z = peak

に `Odd a` を追加した wrapper。
-/
theorem exists_standard_parameter_odd
    {w : Word} {x z : ℕ}
    (M : MountainRun w x z) :
    ∃ a peak : ℕ,
      0 < a ∧
      Odd a ∧
      x = a * 2 ^ M.shape.oddRunLength - 1 ∧
      peak = a * 3 ^ M.shape.oddRunLength - 1 ∧
      2 ^ M.shape.evenRunLength * z = peak := by
  obtain ⟨a, peak, haPos, hx, hPeak, hDesc⟩ :=
    M.exists_standard_parameter
  have hPeakEven : Even peak := by
    have hlPos : 0 < M.shape.evenRunLength :=
      M.shape.evenRunLength_pos
    obtain ⟨r, hr⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlPos)
    refine ⟨2 ^ r * z, ?_⟩
    rw [← hDesc, hr, pow_succ]
    ring
  have haOdd : Odd a := by
    rcases a.even_or_odd' with ⟨b, hab | hab⟩
    · have haEven : Even a := by
        refine ⟨b, ?_⟩
        omega
      have hProdEven :
          Even (a * 3 ^ M.shape.oddRunLength) := by
        rcases haEven with ⟨u, hu⟩
        refine ⟨u * 3 ^ M.shape.oddRunLength, ?_⟩
        rw [hu]
        ring
      rcases hProdEven with ⟨u, hu⟩
      rcases hPeakEven with ⟨v, hv⟩
      have hProdPos :
          0 < a * 3 ^ M.shape.oddRunLength :=
        Nat.mul_pos haPos (Nat.pow_pos (by omega))
      exfalso
      omega
    · refine ⟨b, ?_⟩
      omega
  exact ⟨a, peak, haPos, haOdd, hx, hPeak, hDesc⟩

end MountainRun
end Word
end Collatz2
