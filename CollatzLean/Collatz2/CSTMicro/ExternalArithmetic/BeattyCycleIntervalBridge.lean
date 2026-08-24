import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyCyclicCarryArithmetic
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect


/-!
# Beatty cycle numerator = shifted critical interval numerator

zero-cycle arithmetic で使う

  beattyCyclePhi(s,p)

と Stage 6/7 の interval calculus で使う

  criticalIntervalPhiZ s (s+p)

は、添字を `k=s+u` と取り直した同じ有限和である。
このファイルで両記法を exact に接続する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic


/-- Beatty cycle numerator は同じ start/length の critical interval numerator そのもの。 -/
theorem beattyCyclePhi_eq_criticalIntervalPhiZ
    (s p : ℕ) :
    beattyCyclePhi s p =
      criticalIntervalPhiZ s (s + p) := by
  classical
  unfold beattyCyclePhi criticalIntervalPhiZ
  have hReindex :
      Finset.sum (Finset.Ico s (s + p))
          (fun k =>
            (2 : ℤ) ^ (beattyIndex k - beattyIndex s) *
              (3 : ℤ) ^ (s + p - 1 - k)) =
        Finset.sum (Finset.range p)
          (fun u =>
            (2 : ℤ) ^
                (beattyIndex (s + u) - beattyIndex s) *
              (3 : ℤ) ^ (p - 1 - u)) := by
    symm
    refine Finset.sum_bij (fun u _ => s + u) ?_ ?_ ?_ ?_
    · intro u hu
      have huLt : u < p := Finset.mem_range.mp hu
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro u₁ hu₁ u₂ hu₂ hEq
      omega
    · intro k hk
      have hkIco := Finset.mem_Ico.mp hk
      refine ⟨k - s, Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · omega
    · intro u hu
      have huLt : u < p := Finset.mem_range.mp hu
      have hExp : s + p - 1 - (s + u) = p - 1 - u := by
        omega
      rw [hExp]
  rw [hReindex]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.mem_range] at hu
  ring

/-- 右 endpoint を別名 `b` で持つ wrapper。 -/
theorem beattyCyclePhi_eq_criticalIntervalPhiZ_of_eq_add
    {s p b : ℕ}
    (hb : b = s + p) :
    beattyCyclePhi s p = criticalIntervalPhiZ s b := by
  subst b
  exact beattyCyclePhi_eq_criticalIntervalPhiZ s p

end ExternalArithmetic
end CSTMicro
end Collatz2
