import CollatzLean.Collatz.Word.Geometry

/-!
# first crossing と suffix 収縮

first crossing の proper-prefix expanding と terminal contracting を組み合わせ、
すべての非空 suffix が contracting であることを有限語だけで示す。
-/

namespace Collatz
namespace Word

/-- expanding prefix を持つ contracting append の suffix は contracting。 -/
theorem Contracting.suffix_of_expanding_prefix
    {u v : Collatz.Word}
    (hWhole : (u ++ v).Contracting)
    (hPrefix : u.Expanding) :
    v.Contracting := by
  unfold Word.Contracting at hWhole ⊢
  unfold Word.Expanding at hPrefix
  rw [oddSteps_append, twoSteps_append, pow_add, pow_add] at hWhole
  by_contra hnot
  have hv :
      2 ^ v.twoSteps ≤ 3 ^ v.oddSteps := by
    omega
  have hpowPos : 0 < 2 ^ v.twoSteps :=
    Nat.pow_pos (by omega)
  have hleft :
      2 ^ u.twoSteps * 2 ^ v.twoSteps <
        3 ^ u.oddSteps * 2 ^ v.twoSteps :=
    (Nat.mul_lt_mul_right hpowPos).2 hPrefix
  have hright :
      3 ^ u.oddSteps * 2 ^ v.twoSteps ≤
        3 ^ u.oddSteps * 3 ^ v.oddSteps :=
    Nat.mul_le_mul_left (3 ^ u.oddSteps) hv
  have hcontra :
      2 ^ u.twoSteps * 2 ^ v.twoSteps <
        3 ^ u.oddSteps * 3 ^ v.oddSteps :=
    lt_of_lt_of_le hleft hright
  omega

/-- 全 nonempty suffix の contracting 性から recursive package を作る。 -/
private theorem allSuffixesContracting_of_suffix_property
    (w : Collatz.Word)
    (hSuffix :
      ∀ u v : Collatz.Word,
        w = u ++ v →
        v ≠ [] →
        v.Contracting) :
    w.AllSuffixesContracting := by
  induction w with
  | nil =>
      simp [AllSuffixesContracting]
  | cons e w ih =>
      change Contracting (e :: w) ∧ AllSuffixesContracting w
      constructor
      · exact hSuffix [] (e :: w) (by simp) (by simp)
      · apply ih
        intro u v huv hv
        apply hSuffix (e :: u) v
        · simp [huv]
        · exact hv

/-- first crossing なら全非空 suffix は contracting。 -/
theorem FirstCrossing.allSuffixesContracting
    {w : Collatz.Word}
    (hF : w.FirstCrossing) :
    w.AllSuffixesContracting := by
  apply allSuffixesContracting_of_suffix_property w
  intro u v hdecomp hv
  by_cases hu : u = []
  · subst u
    have hwv : w = v := by
      simpa using hdecomp
    rw [← hwv]
    exact hF.terminalContracting
  · have huPos : 0 < u.length :=
      List.length_pos_of_ne_nil hu
    have hvPos : 0 < v.length :=
      List.length_pos_of_ne_nil hv
    have huLt : u.length < w.length := by
      rw [hdecomp, List.length_append]
      omega
    have hprefixTake : w.take u.length = u := by
      rw [hdecomp]
      simp
    have hprefix : u.Expanding := by
      have h := hF.properExpanding u.length huPos huLt
      simpa [hprefixTake] using h
    have hwhole : (u ++ v).Contracting := by
      rw [← hdecomp]
      exact hF.terminalContracting
    exact hwhole.suffix_of_expanding_prefix hprefix

end Word
end Collatz
