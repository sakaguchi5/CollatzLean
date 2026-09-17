import CollatzLean.Collatz3.Binary.BoundedDefect
import CollatzLean.Collatz3.Binary.Deinterleave


/-!
# Collatz3 Binary: bounded defect と sparse complement

binary word の `0` positions を反転して集めると、Mersenne all-ones word から
欠けている 2冪の和が得られる。

primitive は bitwise complement だけに留め、

`x + missing + 1 = 2^L`

と missing word の one-count が zero defect に一致することを導く。
-/

namespace Collatz3
namespace Binary

/-- LSB-first binary word の bitwise complement。 -/
def complementBits : List Bool → List Bool
  | [] => []
  | b :: bs => (!b) :: complementBits bs

@[simp] theorem complementBits_nil : complementBits [] = [] := rfl

@[simp] theorem complementBits_cons (b : Bool) (bs : List Bool) :
    complementBits (b :: bs) = (!b) :: complementBits bs := rfl

@[simp] theorem complementBits_length (bits : List Bool) :
    (complementBits bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [complementBits, ih]

/-- complement の one-count は元 word の zero-count。 -/
theorem oneCount_complementBits (bits : List Bool) :
    oneCount (complementBits bits) = zeroCount bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [complementBits, zeroCount, ih]

/-- word と complement の値を足すと同じ長さの all-ones になる。 -/
theorem valueLSB_add_complementBits_add_one (bits : List Bool) :
    valueLSB bits + valueLSB (complementBits bits) + 1 =
      2 ^ bits.length := by
  induction bits with
  | nil => simp [complementBits]
  | cons b bs ih =>
      cases b <;>
        simp [complementBits, valueLSB, pow_succ] at ih ⊢ <;>
        omega

namespace HasZeroDefect

/--
exact zero defect は、同じ長さの sparse complement word を与える。
complement word の `1` 数が defect そのものになる。
-/
theorem exists_sparseComplement
    {x defect length : ℕ}
    (h : HasZeroDefect x defect length) :
    ∃ missingBits : List Bool,
      missingBits.length = length ∧
        oneCount missingBits = defect ∧
        x + valueLSB missingBits + 1 = 2 ^ length := by
  rcases h with ⟨bits, hRep, hZero⟩
  refine ⟨complementBits bits, ?_, ?_, ?_⟩
  · calc
      (complementBits bits).length = bits.length := complementBits_length bits
      _ = length := hRep.length
  · simpa [hZero] using oneCount_complementBits bits
  · have hValue := valueLSB_add_complementBits_add_one bits
    rw [hRep.value, hRep.length] at hValue
    exact hValue

end HasZeroDefect

namespace HasZeroDefectAtMost

/-- bounded defect は one-count が同じ bound 以下の sparse complement を与える。 -/
theorem exists_sparseComplement
    {x bound : ℕ}
    (h : HasZeroDefectAtMost x bound) :
    ∃ length : ℕ,
      ∃ missingBits : List Bool,
        missingBits.length = length ∧
          oneCount missingBits ≤ bound ∧
          x + valueLSB missingBits + 1 = 2 ^ length := by
  rcases h with ⟨defect, length, hExact, hLe⟩
  rcases hExact.exists_sparseComplement with
    ⟨missingBits, hLen, hCount, hValue⟩
  refine ⟨length, missingBits, hLen, ?_, hValue⟩
  calc
    oneCount missingBits = defect := hCount
    _ ≤ bound := hLe

end HasZeroDefectAtMost

end Binary
end Collatz3
