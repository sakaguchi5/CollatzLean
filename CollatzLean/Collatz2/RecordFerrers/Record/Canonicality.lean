import CollatzLean.Collatz2.RecordFerrers.Extensions.PublicAPI

/-!
# Record–Ferrers RF-A+2: canonical record theory

`RecordBlock` の strict above/below 条件から、同じ anchor から出る次の record endpoint は
一意であることを示す。そこから record length skeleton の canonicality と、
record decomposition が whole terminal depth を minimal depth に強制することを導く。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace RecordBlock

/-- 同じ fixed fiber / anchor から出る record block の長さは一意。 -/
theorem length_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start r s : ℕ}
    (A : RecordBlock x start r)
    (B : RecordBlock x start s) :
    r = s := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · have hAbove := B.interior_above r A.length_pos hrs
    have hBelow := A.terminal_below
    omega
  · have hAbove := A.interior_above s B.length_pos hsr
    have hBelow := B.terminal_below
    omega

/-- 同じ anchor の二 record blocks は endpoint index も同一。 -/
theorem endpoint_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start r s : ℕ}
    (A : RecordBlock x start r)
    (B : RecordBlock x start s) :
    start + r = start + s := by
  rw [A.length_unique B]

end RecordBlock

namespace RecordChain

/--
同じ fixed fiber / start を覆う二つの genuine record chains は
length skeleton が一致する。
-/
theorem lengths_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {rs ss : List ℕ}
    (C : RecordChain x start rs)
    (D : RecordChain x start ss) :
    rs = ss := by
  induction C generalizing ss with
  | @last start len B hTerminal =>
      cases D with
      | @last _ len' B' hTerminal' =>
          have hLen : len = len' := B.length_unique B'
          subst len'
          rfl
      | @cons _ len' rest B' hInterior' T' =>
          have hLen : len = len' := B.length_unique B'
          subst len'
          omega
  | @cons start len rest B hInterior T ih =>
      cases D with
      | @last _ len' B' hTerminal' =>
          have hLen : len = len' := B.length_unique B'
          subst len'
          omega
      | @cons _ len' rest' B' hInterior' T' =>
          have hLen : len = len' := B.length_unique B'
          subst len'
          have hRest : rest = rest' := ih T'
          subst rest'
          rfl

/--
record chain が存在すると whole terminal depth は必ず
`criticalHeight p + 1` になる。
-/
theorem terminalDepth_eq_minimalDepth
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {rs : List ℕ}
    (C : RecordChain x start rs)
    (hWhole : FirstCrossing x.word) :
    H = minimalDepth p := by
  induction C with
  | @last start len B hTerminal =>
      have hCarry := B.criticalCarry_eq_zero_of_terminal hTerminal hWhole
      have hHeight := height_add_eq_add_blockDepth x start len
      have hLocal := B.local_twoSteps
      have hEndHeight : x.height (start + len) = H := by
        rw [hTerminal]
        exact x.height_terminal
      have hCrit := criticalHeight_add_eq start len
      rw [hCarry] at hCrit
      rw [B.start_roof, hLocal, hEndHeight] at hHeight
      rw [hTerminal] at hCrit
      unfold minimalDepth
      omega
  | cons B hInterior T ih =>
      exact ih

end RecordChain

namespace RecordDecomposition

/-- 同じ `x,start` の record decompositions は length skeleton が一意。 -/
theorem lengths_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (A B : RecordDecomposition x start) :
    A.lengths = B.lengths :=
  A.chain.lengths_unique B.chain

/-- 同じ `x,start` の decomposition は local block slices も一致する。 -/
theorem blocks_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (A B : RecordDecomposition x start) :
    A.blocks = B.blocks := by
  unfold RecordDecomposition.blocks RecordChain.blocks
  rw [A.lengths_unique B]

/-- genuine decomposition から得られる pure skeleton は canonical。 -/
theorem skeleton_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (A B : RecordDecomposition x start) :
    Skeleton.ofDecomposition A = Skeleton.ofDecomposition B := by
  apply Skeleton.eq_of_lengths_eq
  simpa using A.lengths_unique B

/-- record decomposition は whole terminal depth を minimal depth に固定する。 -/
theorem terminalDepth_eq_minimalDepth
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    H = minimalDepth p :=
  D.chain.terminalDepth_eq_minimalDepth D.whole_firstCrossing

/-- record decomposition を持つ whole word 自体が MinimalBlock。 -/
theorem whole_minimalBlock
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    MinimalBlock x.word := by
  refine {
    firstCrossing := D.whole_firstCrossing
    minimalDepth := ?_
  }
  have hTerminal := D.terminalDepth_eq_minimalDepth
  rw [x.twoSteps_eq, x.oddSteps_eq]
  simpa [minimalDepth] using hTerminal

/-- decomposition が存在する fixed fiber では `H = criticalHeight p + 1`。 -/
theorem twoDepth_eq_criticalHeight_add_one
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    H = criticalHeight p + 1 := by
  simpa [minimalDepth] using D.terminalDepth_eq_minimalDepth

end RecordDecomposition

end RecordFerrers
end Collatz2
