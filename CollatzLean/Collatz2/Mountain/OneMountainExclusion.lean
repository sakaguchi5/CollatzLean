import CollatzLean.Collatz2.Mountain.Block
import CollatzLean.Collatz2.Global.EndpointFloorNaturalCoordinates

/-!
# Collatz2 Mountain: one-mountain paradoxical return exclusion

Rozier--Terracol Appendix A の「一つの local maximum しか持たない
acyclic paradoxical sequence は存在しない」を、Collatz2 の odd-only mountain
へ直接移した elementary 版。

一 mountain

  [1^r,d], d>=2

の actual run x -> z が positive (`x < z`) なら、standard odd/even counts
k=r+1, l=d-1 に対して必ず

  2^(k+l) < 3^k

となる。従って同じ word が Contracting

  3^k < 2^(k+l)

であることとは両立しない。
-/

namespace Collatz2
namespace Word
namespace MountainRun

/-- positive actual mountain は coefficient-expanding。 -/
theorem expanding_of_positive
    {w : Word} {x z : ℕ}
    (M : MountainRun w x z)
    (hPositive : x < z) :
    Word.Expanding w := by
  apply (Word.expanding_iff_twoPow_lt_threePow).2
  obtain ⟨a, peak, ha, hx, hpeak, hdesc⟩ :=
    M.exists_standard_parameter
  have hxAdd :
      x + 1 =
        a * 2 ^ M.shape.oddRunLength := by
    have hpos :
        0 < a * 2 ^ M.shape.oddRunLength :=
      Nat.mul_pos ha (Nat.pow_pos (by omega))
    have hx' :
        x + 1 =
          (a * 2 ^ M.shape.oddRunLength - 1) + 1 :=
      congrArg (fun t : ℕ => t + 1) hx
    calc
      x + 1 =
          (a * 2 ^ M.shape.oddRunLength - 1) + 1 :=
        hx'
      _ = a * 2 ^ M.shape.oddRunLength := by
        omega
  have hzLower :
      a * 2 ^ M.shape.oddRunLength ≤ z := by
    calc
      a * 2 ^ M.shape.oddRunLength
          = x + 1 := hxAdd.symm
      _ ≤ z := by
        omega
  have hleft :
      a * 2 ^
          (M.shape.oddRunLength + M.shape.evenRunLength)
        ≤
      2 ^ M.shape.evenRunLength * z := by
    calc
      a * 2 ^
          (M.shape.oddRunLength + M.shape.evenRunLength)
          =
          2 ^ M.shape.evenRunLength *
            (a * 2 ^ M.shape.oddRunLength) := by
              rw [pow_add]
              ring
      _ ≤ 2 ^ M.shape.evenRunLength * z :=
        Nat.mul_le_mul_left
          (2 ^ M.shape.evenRunLength)
          hzLower
  have hright :
      2 ^ M.shape.evenRunLength * z
        <
      a * 3 ^ M.shape.oddRunLength := by
    calc
      2 ^ M.shape.evenRunLength * z
          = peak :=
        hdesc
      _ < a * 3 ^ M.shape.oddRunLength := by
        have hpos :
            0 < a * 3 ^ M.shape.oddRunLength :=
          Nat.mul_pos ha (Nat.pow_pos (by omega))
        have hpeak' := hpeak
        rw [hpeak']
        omega
  have hscaled :
      a * 2 ^
          (M.shape.oddRunLength + M.shape.evenRunLength)
        <
      a * 3 ^ M.shape.oddRunLength :=
    lt_of_le_of_lt hleft hright
  have hcoeff :
      2 ^
          (M.shape.oddRunLength + M.shape.evenRunLength)
        <
      3 ^ M.shape.oddRunLength :=
    (Nat.mul_lt_mul_left ha).mp hscaled
  rw [M.shape.twoSteps_eq, M.shape.oddSteps_eq]
  exact hcoeff

/-- positive actual mountain と Contracting は両立しない。 -/
theorem not_contracting_of_positive
    {w : Word} {x z : ℕ}
    (M : MountainRun w x z)
    (hPositive : x < z) :
    ¬ Word.Contracting w := by
  intro hC
  exact Word.not_expanding_and_contracting w
    ⟨M.expanding_of_positive hPositive, hC⟩

end MountainRun
end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- current A obstruction 全体は一 mountain ではあり得ない。 -/
theorem not_oneMountain
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    ¬ Word.OneMountain D.word := by
  rintro ⟨Mshape⟩
  let M : Word.MountainRun D.word
      (O.value D.startIndex)
      (O.value D.endIndex) := {
    shape := Mshape
    run := D.runs
  }
  exact
    M.not_contracting_of_positive
      (by simpa [endIndex] using D.positive)
      D.contracting

/--
mountain decomposition が与えられれば current A は最低2 mountain を持つ。

これは Rozier--Terracol Appendix A の one-local-maximum exclusion の
odd-only current-A specialization。
-/
theorem mountainCount_ge_two
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (C : Word.MountainDecomposition D.word) :
    2 ≤ C.mountainCount := by
  have hpos : 0 < C.mountainCount :=
    C.count_pos_of_word_nonempty D.word_nonempty
  by_contra hnot
  have hle : C.mountainCount ≤ 1 := by omega
  have hOne : C.mountainCount = 1 := by omega
  exact D.not_oneMountain (C.oneMountain_of_count_eq_one hOne)

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
