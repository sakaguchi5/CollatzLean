import CollatzLean.Collatz3.Semantics.Runs
import CollatzLean.Collatz3.Critical.FirstPassage

/-!
# Collatz3: actual critical first-passage run

pure coefficient geometry `Word.CriticalFirstPassage` と actual `Runs` を
薄い conjunction で接続する。profile / canonical data はここに保存しない。
-/

namespace Collatz3

/-- actual odd-only run であり、その exponent word が critical first-passage。 -/
def ActualFirstPassage
    (w : Word)
    (x y : ℕ) : Prop :=
  Runs w x y ∧ Word.CriticalFirstPassage w

namespace ActualFirstPassage

/-- actual first-passage は actual run。 -/
theorem run
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Runs w x y :=
  h.1

/-- actual first-passage の pure coefficient geometry。 -/
theorem critical
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Word.CriticalFirstPassage w :=
  h.2

/-- actual first-passage word は valid。 -/
theorem valid
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Word.Valid w :=
  h.run.valid

/-- actual first-passage word は非空。 -/
theorem word_nonempty
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    w ≠ [] :=
  h.critical.nonempty

end ActualFirstPassage
end Collatz3
