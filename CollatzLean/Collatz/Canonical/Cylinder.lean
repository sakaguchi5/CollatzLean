import CollatzLean.Collatz.FiniteOrbit.Reconstruction
import CollatzLean.Collatz.Canonical.Replay

/-!
# canonical cylinderのactual復元とdigit分解

valid有限語のcanonical affine解をactual odd runへ復元する。
さらに語を右へ延長したとき、canonical startの変化を
旧prefixのcanonical modulusを基数とする明示digitで表す。
-/

namespace Collatz
namespace Word

/-- valid語のcanonical start/endはactual odd runをなす。 -/
theorem Valid.canonicalRuns
    {w : Collatz.Word} (hvalid : w.Valid) :
    Runs w w.canonicalStart w.canonicalEnd := by
  exact hvalid.runs_of_realizes
    w.canonicalEnd_realizes
    w.canonicalEnd_odd

/-- 右延長語のcanonical startを旧prefix modulusで割ったquotient。 -/
def extensionDigit (u v : Collatz.Word) : ℕ :=
  (u ++ v).canonicalStart / u.residueModulus

/--
非空valid prefixを右へ延長すると、延長後canonical startは
旧canonical startと同じ旧modulus剰余を持つ。
-/
theorem canonicalStart_append_mod
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    (u ++ v).canonicalStart % u.residueModulus = u.canonicalStart := by
  have hrun :
      Runs (u ++ v) (u ++ v).canonicalStart (u ++ v).canonicalEnd :=
    hvalid.canonicalRuns
  obtain ⟨y, hprefix, _hsuffix⟩ := hrun.split_append
  have hy : Odd y := hprefix.end_odd_of_ne_nil hu
  exact hprefix.realizes.start_mod_eq_canonicalStart hy

/--
canonical cylinder digitによる右延長startの完全分解。
`next = current + modulus * digit`。
-/
theorem canonicalStart_append_eq
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    (u ++ v).canonicalStart =
      u.canonicalStart + u.residueModulus * u.extensionDigit v := by
  have hmod := canonicalStart_append_mod hvalid hu
  have hdecomp := Nat.mod_add_div (u ++ v).canonicalStart u.residueModulus
  rw [hmod] at hdecomp
  unfold extensionDigit
  simpa [Nat.mul_comm] using hdecomp.symm

/-- 一文字`e`の右延長ではcylinder digitは`2^e`未満。 -/
theorem extensionDigit_singleton_lt_twoPow
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    u.extensionDigit [e] < 2 ^ e := by
  have hmodulus :
      (u ++ [e]).residueModulus = u.residueModulus * 2 ^ e := by
    simp [residueModulus, pow_add, Nat.add_comm,
      Nat.add_left_comm, Nat.mul_comm]
  have hstartLt :
      (u ++ [e]).canonicalStart < u.residueModulus * 2 ^ e := by
    rw [← hmodulus]
    exact canonicalStart_lt_modulus (u ++ [e])
  have hdecomp := canonicalStart_append_eq hvalid hu
  by_contra hnot
  have hdigit : 2 ^ e ≤ u.extensionDigit [e] :=
    Nat.le_of_not_gt hnot
  have hmul :
      u.residueModulus * 2 ^ e ≤
        u.residueModulus * u.extensionDigit [e] :=
    Nat.mul_le_mul_left u.residueModulus hdigit
  have hmulLe :
      u.residueModulus * u.extensionDigit [e] ≤
        (u ++ [e]).canonicalStart := by
    rw [hdecomp]
    omega
  omega

end Word
end Collatz
