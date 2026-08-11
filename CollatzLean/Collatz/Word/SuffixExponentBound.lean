import CollatzLean.Collatz.Word.Geometry

/-!
# all-suffix contracting から得る suffix cumulative exponent bounds

`AllSuffixesContracting w` は、任意の非空 drop suffix が contracting であることを意味する。
従って各 suffix の cumulative two-step exponent `K` は

  `3^r < 2^K`

を満たす。bidirectional decoder の backward constraint として使う。
-/

namespace Collatz
namespace Word

/-- all-suffix-contracting は任意の drop tail に保存される。 -/
theorem AllSuffixesContracting.drop
    {w : Collatz.Word}
    (h : AllSuffixesContracting w) (k : ℕ) :
    AllSuffixesContracting (w.drop k) := by
  induction k generalizing w with
  | zero => simpa
  | succ k ih =>
      cases w with
      | nil => simp [AllSuffixesContracting]
      | cons e w =>
          change Contracting (e :: w) ∧ AllSuffixesContracting w at h
          simpa using ih h.2

/-- 任意の非空 drop suffix は contracting。 -/
theorem AllSuffixesContracting.drop_contracting
    {w : Collatz.Word}
    (h : AllSuffixesContracting w)
    {k : ℕ}
    (hk : k < w.length) :
    Contracting (w.drop k) := by
  have hdrop := h.drop k
  apply hdrop.whole
  apply List.ne_nil_of_length_pos
  simp
  omega

/--
任意の非空 drop suffix に対する cumulative exponent inequality。
-/
theorem AllSuffixesContracting.threePow_drop_lt_twoPow_drop
    {w : Collatz.Word}
    (h : AllSuffixesContracting w)
    {k : ℕ}
    (hk : k < w.length) :
    3 ^ oddSteps (w.drop k) < 2 ^ twoSteps (w.drop k) := by
  exact h.drop_contracting hk

/--
後ろから `r` 文字の suffix の cumulative exponent は `3^r` を越えるだけの2冪を持つ。
-/
theorem AllSuffixesContracting.lastSuffix_threePow_lt_twoPow
    {w : Collatz.Word}
    (h : AllSuffixesContracting w)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ w.length) :
    3 ^ r < 2 ^ twoSteps (w.drop (w.length - r)) := by
  have hk : w.length - r < w.length := by
    omega
  have hc := h.threePow_drop_lt_twoPow_drop hk
  have hlen : oddSteps (w.drop (w.length - r)) = r := by
    simp [oddSteps, Nat.sub_sub_self hrLe]
  simpa [hlen] using hc

end Word
end Collatz
