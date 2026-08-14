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

namespace MountainDecomposition

/--
末尾 exponent が `2` 以上の valid word は完全 mountain 列へ分解できる。

既存 `MountainDecomposition` の shape を変えず、左端 exponent を再帰的に
suffix decomposition へ戻す。`1` なら先頭 mountain の rise に吸収し、
`2` 以上なら singleton mountain として前置する。
-/
theorem exists_of_valid_append_singleton
    (u : Word)
    {d : ℕ}
    (hValid : Valid (u ++ [d]))
    (hd : 2 ≤ d) :
    Nonempty (MountainDecomposition (u ++ [d])) := by
  induction u with
  | nil =>
      let M : MountainBlock ([d] : Word) := {
        riseCount := 0
        dropExponent := d
        drop_ge_two := hd
        word_eq := by simp
      }
      exact ⟨{
        blocks := [[d]]
        shape := by
          intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          subst b
          exact ⟨M⟩
        decomp := by simp
      }⟩
  | cons e u ih =>
      have hePos : 0 < e := by
        apply hValid e
        simp
      have hTailValid : Valid (u ++ [d]) := by
        intro a ha
        apply hValid a
        simp only [List.cons_append, List.mem_cons]
        exact Or.inr ha
      obtain ⟨C⟩ := ih hTailValid
      by_cases heOne : e = 1
      · subst e
        cases hblocks : C.blocks with
        | nil =>
            have hTailNe : u ++ [d] ≠ [] := by simp
            have hEq := C.decomp
            rw [hblocks] at hEq
            simp at hEq
        | cons b bs =>
            have hbMem : b ∈ C.blocks := by
              rw [hblocks]
              simp
            obtain ⟨Mb⟩ := C.shape b hbMem
            let Mb' : MountainBlock (1 :: b) := {
              riseCount := Mb.riseCount + 1
              dropExponent := Mb.dropExponent
              drop_ge_two := Mb.drop_ge_two
              word_eq := by
                calc
                  1 :: b =
                      1 :: (List.replicate Mb.riseCount 1 ++ [Mb.dropExponent]) := by
                        exact congrArg (fun xs : Word => 1 :: xs) Mb.word_eq
                  _ =
                      List.replicate (Mb.riseCount + 1) 1 ++ [Mb.dropExponent] := by
                        simp [List.replicate_succ]
            }
            let C' : MountainDecomposition ((1 :: u) ++ [d]) := {
              blocks := (1 :: b) :: bs
              shape := by
                intro c hc
                simp only [List.mem_cons] at hc
                rcases hc with rfl | hc
                · exact ⟨Mb'⟩
                · apply C.shape c
                  rw [hblocks]
                  simp [hc]
              decomp := by
                have hEq : b ++ bs.flatten = u ++ [d] := by
                  have h := C.decomp
                  rw [hblocks] at h
                  simpa using h
                change (1 :: b) ++ bs.flatten = (1 :: u) ++ [d]
                simpa using congrArg (fun xs : Word => 1 :: xs) hEq
            }
            exact ⟨C'⟩
      · have heTwo : 2 ≤ e := by omega
        let Me : MountainBlock ([e] : Word) := {
          riseCount := 0
          dropExponent := e
          drop_ge_two := heTwo
          word_eq := by simp
        }
        let C' : MountainDecomposition ((e :: u) ++ [d]) := {
          blocks := [e] :: C.blocks
          shape := by
            intro c hc
            simp only [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact ⟨Me⟩
            · exact C.shape c hc
          decomp := by
            change [e] ++ C.blocks.flatten = (e :: u) ++ [d]
            rw [C.decomp]
            simp
        }
        exact ⟨C'⟩

end MountainDecomposition
end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
current A の FirstCrossing word は無条件に完全 mountain 列へ分解できる。

最後の exponent が `1` なら、非空の直前 prefix がある場合は
proper-prefix Expanding と whole Contracting が衝突する。
直前 prefix が空の場合も singleton `[1]` 自身は Contracting ではない。
従って最後は `2` 以上である。
-/
theorem exists_mountainDecomposition
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Nonempty (Word.MountainDecomposition D.word) := by
  rcases D.word.eq_nil_or_concat' with hNil | ⟨u, d, hWord⟩
  · exact False.elim (D.word_nonempty hNil)
  · have hdPos : 0 < d := by
      apply D.word_valid d
      rw [hWord]
      simp
    have hdTwo : 2 ≤ d := by
      by_contra hnot
      have hdOne : d = 1 := by omega
      subst d
      by_cases huNil : u = []
      · subst u
        have hC :=
          (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
        rw [hWord] at hC
        norm_num [Word.oddSteps, Word.twoSteps] at hC
      · have huPos : 0 < u.length :=
          List.length_pos_iff.mpr huNil
        have huLt : u.length < D.word.length := by
          rw [hWord]
          simp
        have hF : Word.FirstCrossing D.word := by
          simpa [CanonicalEndpointFloorContractingReturn.word] using
            D.firstCrossing
        have hTake : D.word.take u.length = u := by
          rw [hWord]
          simp
        have hExpU : Word.Expanding u := by
          have hExp := hF.properExpanding huPos huLt
          simpa [hTake] using hExp
        have hExpPow :
            2 ^ Word.twoSteps u < 3 ^ Word.oddSteps u :=
          (Word.expanding_iff_twoPow_lt_threePow).1 hExpU
        have hConPow :
            3 ^ Word.oddSteps (u ++ [1]) <
              2 ^ Word.twoSteps (u ++ [1]) := by
          have hC :=
            (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
          simpa [hWord] using hC
        simp [Word.oddSteps, Word.twoSteps, pow_succ] at hConPow
        simp [Word.oddSteps, Word.twoSteps] at hExpPow
        have hThreePos :
            0 < 3 ^ u.length := by
          positivity
        linarith
    have hValid : Word.Valid (u ++ [d]) := by
      rw [← hWord]
      exact D.word_valid
    have hM :
        Nonempty (Word.MountainDecomposition (u ++ [d])) :=
      Word.MountainDecomposition.exists_of_valid_append_singleton
        u hValid hdTwo
    rw [hWord]
    exact hM

/-- current A に付随する mountain decomposition を一つ選ぶ。 -/
noncomputable def mountainDecomposition
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.MountainDecomposition D.word := by
  classical
  exact Classical.choice D.exists_mountainDecomposition

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

/-- current A から実際に選んだ decomposition も最低2山。 -/
theorem mountainDecomposition_count_ge_two
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    2 ≤ D.mountainDecomposition.mountainCount :=
  D.mountainCount_ge_two D.mountainDecomposition

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
