import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordPartition

/-!
# Collatz3 Experimental2: canonical record partition の純データ inverse

`RecordPartition` で得た strict cut 列と block length 列の間の有限変換を閉じる。

ここでは rank の性質、屋根算術、carry、admissibility を一切使わない。
`blockLengthsFromCuts` で cut 列を隣接差へ変換し、`cutsFromBlockLengths` で
proper endpoint 列へ戻す。この二つが strict cut chain 上で exact inverse になることを示す。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
block length 列から terminal を除いた proper endpoint cut 列を復元する。

`[r₁,r₂,...,rₙ]` を start `a` から読むと、
`[a+r₁, a+r₁+r₂, ...]` のうち terminal 直前までを返す。
-/
def cutsFromBlockLengths : ℕ → List ℕ → List ℕ
  | _a, [] => []
  | _a, [_r] => []
  | a, r :: s :: rs =>
      (a + r) :: cutsFromBlockLengths (a + r) (s :: rs)

/--
strict cut chain を隣接差へ変換してから endpoint を復元すると、元の cut 列に exact に戻る。
-/
theorem cutsFromBlockLengths_blockLengthsFromCuts
    {terminal a : ℕ}
    {cuts : List ℕ}
    (C : StrictCutChainFrom terminal a cuts) :
    cutsFromBlockLengths a (blockLengthsFromCuts terminal a cuts) = cuts := by
  induction cuts generalizing a with
  | nil =>
      simp [blockLengthsFromCuts, cutsFromBlockLengths]
  | cons k ks ih =>
      simp only [StrictCutChainFrom] at C
      have hak : a < k := C.1
      have hIndex : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      have hIH := ih (a := k) C.2.2
      let tailLengths := blockLengthsFromCuts terminal k ks
      have hTailNe : tailLengths ≠ [] := by
        dsimp [tailLengths]
        exact blockLengthsFromCuts_ne_nil terminal k ks
      cases hTail : tailLengths with
      | nil =>
          exact False.elim (hTailNe hTail)
      | cons s ss =>
          change
            cutsFromBlockLengths a
                ((k - a) :: tailLengths) = k :: ks
          rw [hTail]
          simp only [cutsFromBlockLengths]
          rw [hIndex]
          change cutsFromBlockLengths k tailLengths = ks at hIH
          simpa [hTail] using congrArg (List.cons k) hIH

/--
正の非空 length 列が start から terminal を exact に覆うなら、
endpoint cut 列を作って再び隣接差を取ると元の length 列に戻る。
-/
theorem blockLengthsFromCuts_cutsFromBlockLengths
    {terminal a : ℕ}
    {rs : List ℕ}
    (hne : rs ≠ [])
    (hPos : ∀ r ∈ rs, 0 < r)
    (hEnd : a + rs.sum = terminal) :
    blockLengthsFromCuts terminal a (cutsFromBlockLengths a rs) = rs := by
  induction rs generalizing a with
  | nil =>
      exact False.elim (hne rfl)
  | cons r rs ih =>
      cases rs with
      | nil =>
          have hr : terminal - a = r := by
            simp at hEnd
            omega
          simp [cutsFromBlockLengths, blockLengthsFromCuts, hr]
      | cons s ss =>
          have hTailPos : ∀ q ∈ s :: ss, 0 < q := by
            intro q hq
            exact hPos q (by simp [hq])
          have hTailEnd :
              (a + r) + (s :: ss).sum = terminal := by
            simpa [Nat.add_assoc] using hEnd
          have hIH :=
            ih (a := a + r)
              (by simp)
              hTailPos
              hTailEnd
          simp [cutsFromBlockLengths, blockLengthsFromCuts, hIH]

/--
canonical record lengths から proper endpoint を戻すと、
deterministic `canonicalRecordCuts` そのものに exact に戻る。
-/
theorem cutsFromCanonicalRecordLengths_eq_canonicalRecordCuts
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (hm : 1 < m) :
    cutsFromBlockLengths canonicalAnchor
        (canonicalRecordLengths β m height) =
      canonicalRecordCuts β m height := by
  unfold canonicalRecordLengths recordLengthsAfter canonicalRecordCuts
  exact
    cutsFromBlockLengths_blockLengthsFromCuts
      (recordCutsAfter_strictCutChain
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor)
        (by simpa [canonicalAnchor] using hm))

end GenericRecordFerrers
end Experimental2
end Collatz3
