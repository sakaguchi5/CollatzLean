import CollatzLean.Collatz3.Critical.WordProfileEquiv
import Mathlib.Tactic.NormNum

/-!
# Collatz3: critical roof anchor

Record--Ferrers の開始点を `0` に固定すると、global chord rank は
start と terminal の両方で `0` になり、terminal を strict record drop として
扱えない。

旧設計で使っていた正の anchor を、ここでは pure critical profile から
導かれる概念として切り出す。

重要なのは actual future-minimum と混同しないことである。

* `IsRoofCut` は Word/Profile の純粋な係数幾何。
* future-minimum は actual orbit の値に関する意味論。

両者の接続は Bridge 層で行う。
-/

namespace Collatz3
namespace Critical

/-- current critical geometry で使う canonical initial roof anchor。 -/
def initialRoofAnchor : ℕ := 1

@[simp] theorem initialRoofAnchor_eq_one :
    initialRoofAnchor = 1 :=
  rfl

/-- `beattyIndex 1 = 1`。初期 anchor `[1]` の基礎となる小さい算術事実。 -/
@[simp] theorem beattyIndex_one :
    beattyIndex 1 = 1 := by
  have hLe : beattyIndex 1 ≤ 1 := by
    apply beattyIndex_le_of_upper
    norm_num
  have hUpper := beattyIndex_upper 1
  by_cases hZero : beattyIndex 1 = 0
  · rw [hZero] at hUpper
    norm_num at hUpper
  · omega

/--
proper cut `a` が critical roof 上にあること。

`profileHeight h a = beattyIndex a` は、この cut で Ferrers deficit が 0、
すなわち prefix two-depth が critical roof に exact に乗ることを表す。
-/
def IsRoofCut
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) : Prop :=
  0 < a ∧
    a < m ∧
    profileHeight h a = beattyIndex a

namespace IsRoofCut

/-- roof cut は正の index。 -/
theorem pos
    {m : ℕ}
    {h : Profile m}
    {a : ℕ}
    (A : IsRoofCut h a) :
    0 < a :=
  A.1

/-- roof cut は terminal より手前。 -/
theorem lt_width
    {m : ℕ}
    {h : Profile m}
    {a : ℕ}
    (A : IsRoofCut h a) :
    a < m :=
  A.2.1

/-- roof cut の prefix height は Beatty roof に exact に一致。 -/
theorem height_eq
    {m : ℕ}
    {h : Profile m}
    {a : ℕ}
    (A : IsRoofCut h a) :
    profileHeight h a = beattyIndex a :=
  A.2.2

end IsRoofCut

/--
幅が 2 以上の admissible profile では cut `1` の prefix height は exact に `1`。

checkpoint `0 = 0`、checkpoint の strict 増加、`beattyIndex 1 = 1`
の三つだけから出る。
-/
theorem profileHeight_one_eq_one
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m) :
    profileHeight h 1 = 1 := by
  rw [profileHeight_of_lt h hm]
  have hStrict := A.checkpoint_strict (k := 0) hm
  have hZero :
      checkpoint h ⟨0, by omega⟩ = 0 :=
    A.first_checkpoint_eq_zero (by omega)
  rw [hZero] at hStrict
  have hPos :
      0 < checkpoint h ⟨1, hm⟩ := by
    simpa using hStrict
  have hLe :
      checkpoint h ⟨1, hm⟩ ≤ beattyIndex 1 := by
    unfold checkpoint
    exact Nat.sub_le _ _
  rw [beattyIndex_one] at hLe
  omega

/-- 幅が 2 以上なら、admissible profile の column `1` deficit は 0。 -/
theorem profileDepth_one_eq_zero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m) :
    h ⟨1, hm⟩ = 0 := by
  have hHeight := profileHeight_one_eq_one A hm
  rw [profileHeight_of_lt h hm] at hHeight
  unfold checkpoint at hHeight
  rw [beattyIndex_one] at hHeight
  have hLe := A.depth_le ⟨1, hm⟩
  rw [beattyIndex_one] at hLe
  omega

/--
幅が 2 以上の admissible profile では `1` が canonical positive roof anchor。
これは record cut の vacuous な最初の要素ではなく、分解の開始基準点である。
-/
theorem initialRoofAnchor_isRoofCut
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m) :
    IsRoofCut h initialRoofAnchor := by
  refine ⟨by simp [initialRoofAnchor], by simpa [initialRoofAnchor] using hm, ?_⟩
  simpa [initialRoofAnchor, beattyIndex_one] using
    profileHeight_one_eq_one A hm

namespace IsCriticalWord

/--
幅が 2 以上の critical word では最初の prefix two-depth は exact に `1`。
profile を経由せず、valid 性と Beatty roof bound から直接導く。
-/
theorem prefixTwoDepth_one_eq_one
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w)
    (hm : 1 < m) :
    Word.prefixTwoDepth w 1 = 1 := by
  have hLe := C.prefixTwoDepth_le_beatty (k := 1) hm
  rw [beattyIndex_one] at hLe
  have hPos : 0 < Word.prefixTwoDepth w 1 := by
    have hStep := Word.prefixTwoDepth_lt_succ_of_valid
      C.valid (k := 0) (by rw [C.oddSteps_eq]; omega)
    simpa using hStep
  omega

/--
幅が 2 以上の critical word は exact に `[1]` から始まる。
旧 Record--Ferrers の positive anchor `[1]` を pure shape 側で回収する定理。
-/
theorem exists_tail_eq_one_cons
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w)
    (hm : 1 < m) :
    ∃ tail : Word, w = 1 :: tail := by
  cases w with
  | nil =>
      have hLen := C.oddSteps_eq
      simp [Word.oddSteps] at hLen
      omega
  | cons e tail =>
      have hDepth := C.prefixTwoDepth_one_eq_one hm
      have he : e = 1 := by
        simpa [Word.prefixTwoDepth, Word.twoSteps] using hDepth
      subst e
      exact ⟨tail, rfl⟩

end IsCriticalWord

end Critical
end Collatz3
