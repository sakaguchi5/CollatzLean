import CollatzLean.Collatz2.Mountain.Block
import CollatzLean.Collatz2.Geometry.MinimalCrossingBlock
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Mountain: record/minimal-crossing bridge

value-space mountain `[1^r,d]` と coefficient/rank-space minimal crossing block を接続する。
一つの record block は一般には複数 mountain を含み得る。
-/

namespace Collatz2
namespace Word

namespace MountainDecomposition

/--
末尾 exponent が `2` 以上の valid word は完全 mountain 列へ分解できる一般版。
current A に依存しない。
-/
theorem exists_of_valid_ending_ge_two
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
                  _ = List.replicate (Mb.riseCount + 1) 1 ++ [Mb.dropExponent] := by
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

/-- valid FirstCrossing word の最後の exponent は必ず `2` 以上。 -/
theorem FirstCrossing.lastExponent_ge_two
    {w u : Word}
    {d : ℕ}
    (hF : FirstCrossing w)
    (hValid : Valid w)
    (hWord : w = u ++ [d]) :
    2 ≤ d := by
  have hdPos : 0 < d := by
    apply hValid d
    rw [hWord]
    simp
  by_contra hnot
  have hdOne : d = 1 := by omega
  subst d
  by_cases huNil : u = []
  · subst u
    have hC :=
      (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
    rw [hWord] at hC
    norm_num [oddSteps, twoSteps] at hC
  · have huPos : 0 < u.length := List.length_pos_iff.mpr huNil
    have huLt : u.length < w.length := by
      rw [hWord]
      simp
    have hTake : w.take u.length = u := by
      rw [hWord]
      simp
    have hExpU : Expanding u := by
      have hExp := hF.properExpanding huPos huLt
      simpa [hTake] using hExp
    have hExpPow : 2 ^ twoSteps u < 3 ^ oddSteps u :=
      (expanding_iff_twoPow_lt_threePow).1 hExpU
    have hConPow :
        3 ^ oddSteps (u ++ [1]) < 2 ^ twoSteps (u ++ [1]) := by
      have hC :=
        (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
      simpa [hWord] using hC
    simp [oddSteps, twoSteps, pow_succ] at hConPow
    simp [oddSteps, twoSteps] at hExpPow
    have hThreePos : 0 < 3 ^ u.length := by positivity
    linarith

namespace ValidMinimalCrossingBlock

/-- valid minimal record block は one-or-more value mountains へ分解できる。 -/
theorem exists_mountainDecomposition
    {w : Word}
    (M : ValidMinimalCrossingBlock w) :
    Nonempty (MountainDecomposition w) := by
  rcases w.eq_nil_or_concat' with hNil | ⟨u, d, hWord⟩
  · exact False.elim (M.toMinimalCrossingBlock.nonempty hNil)
  · have hdTwo :=
      M.toMinimalCrossingBlock.firstCrossing.lastExponent_ge_two
        M.valid hWord
    have hValid : Valid (u ++ [d]) := by
      rw [← hWord]
      exact M.valid
    have hD := MountainDecomposition.exists_of_valid_ending_ge_two u hValid hdTwo
    rw [hWord]
    exact hD

/-- one value-mountain でもある minimal block の drop exponent は total critical depth で固定。 -/
theorem oneMountain_dropEquation
    {w : Word}
    (M : ValidMinimalCrossingBlock w)
    (hOne : OneMountain w) :
    ∃ S : MountainBlock w,
      S.riseCount + S.dropExponent = criticalHeight (oddSteps w) + 1 := by
  rcases hOne with ⟨S⟩
  refine ⟨S, ?_⟩
  have hTwo := S.twoSteps_eq
  have hMin := M.toMinimalCrossingBlock.minimalDepth
  rw [hMin] at hTwo
  unfold MountainBlock.oddRunLength MountainBlock.evenRunLength at hTwo
  have hd := S.drop_ge_two
  omega

end ValidMinimalCrossingBlock

end Word
end Collatz2
