import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHighBranchChecks

/-! 認証済み10枝の結果を有限集合についてまとめる。 -/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

theorem highBranches_checked {a : Nat}
    (ha : a ∈ [65,62,59,56,54,51,48,46,43,40]) :
    familyCheck 1000 (rootFamily a)=true := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact branch65_checked
  · exact branch62_checked
  · exact branch59_checked
  · exact branch56_checked
  · exact branch54_checked
  · exact branch51_checked
  · exact branch48_checked
  · exact branch46_checked
  · exact branch43_checked
  · exact branch40_checked

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
