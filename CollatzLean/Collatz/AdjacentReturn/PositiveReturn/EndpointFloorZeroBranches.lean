import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroPacket
import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.FirstOvershootSaturation

/-!
# endpoint-floor zero packet の最終二枝

`EndpointFloorZero.Packet` では

* `S < T < s`
* natural 型 coordinate `n,d`
* `6*n+2 <= tailLength`
* whole FirstCrossing
* all-suffix-contracting
* 全 interior boundary `> T`
* inner replay quotient `0`

が同時に成立する。

その結果 tail の先頭 exponent は `1` または `2` しかない。
このファイルでは両枝に forward arithmetic と backward strict-center API を載せ、
Contracting 側の未証明数学を二つの branch exclusion Prop だけへ固定する。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero

/-- `e=1` 最終枝。 -/
structure E1BranchData
    (v : Collatz.Word) (boundary n d : ℕ) (u : Collatz.Word) : Prop where
  packet : Packet v boundary
  coordinates : CoordinateData v n d
  tail_eq : v = 1 :: u

/-- `e=2` 最終枝。 -/
structure E2BranchData
    (v : Collatz.Word) (boundary n d : ℕ) (u : Collatz.Word) : Prop where
  packet : Packet v boundary
  coordinates : CoordinateData v n d
  tail_eq : v = 2 :: u

namespace E1BranchData

/-- e=1 branch の tail first step。 -/
theorem firstTailStep
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E1BranchData v boundary n d u) :
    ∃ y : ℕ,
      Word.Runs ([1] : Collatz.Word)
        (Word.canonicalStart v) y ∧
      Odd y ∧
      y = 9 * (n + d) - 1 := by
  have hvalid := B.packet.tail_valid
  have hrun :
      Word.Runs v (Word.canonicalStart v) (Word.canonicalEnd v) :=
    hvalid.canonicalRuns
  rw [B.tail_eq] at hrun
  have hdecomp : (1 :: u) = ([1] : Collatz.Word) ++ u := by simp
  rw [hdecomp] at hrun
  obtain ⟨y, hhead, _⟩ := hrun.split_append
  have hreal := hhead.realizes
  have hstep :
      2 * y = 3 * Word.canonicalStart v + 1 := by
    rw [B.tail_eq]
    simpa [
      Word.Realizes,
      Word.twoSteps,
      Word.oddSteps,
      Word.affineConst
    ] using hreal
  have hs := B.coordinates.tailStart_add_one
  have hy : y = 9 * (n + d) - 1 := by
    omega
  exact ⟨y, by simpa [B.tail_eq] using hhead, hhead.end_odd, hy⟩

/-- e=1 では `q=n+d` は偶数。 -/
theorem coordinateSum_even
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E1BranchData v boundary n d u) :
    ∃ k : ℕ, n + d = k + k := by
  obtain ⟨y, _hrun, hyOdd, hy⟩ := B.firstTailStep
  rcases hyOdd with ⟨a, ha⟩
  have hEq : 2 * a + 1 = 9 * (n + d) - 1 := by
    rw [← ha, hy]
  obtain ⟨k, hEven | hOdd⟩ := (n + d).even_or_odd'
  · refine ⟨k, ?_⟩
    omega
  · rw [hOdd] at hEq
    omega

/-- e=1 branch でも全 backward depth の strict-center inequality が使える。 -/
theorem backwardStrictCenter
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E1BranchData v boundary n d u)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ v.length) :
    Word.affineConst (v.drop (v.length - r)) <
      Word.contractingGap (v.drop (v.length - r)) *
        Word.canonicalEnd (1 :: v) :=
  B.packet.tailSuffix_strictCenter hrPos hrLe

end E1BranchData

namespace E2BranchData

/-- e=2 branch の tail first step。 -/
theorem firstTailStep
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    ∃ y : ℕ,
      Word.Runs ([2] : Collatz.Word)
        (Word.canonicalStart v) y ∧
      Odd y ∧
      2 * y = 9 * (n + d) - 1 := by
  have hvalid := B.packet.tail_valid
  have hrun :
      Word.Runs v (Word.canonicalStart v) (Word.canonicalEnd v) :=
    hvalid.canonicalRuns
  rw [B.tail_eq] at hrun
  have hdecomp : (2 :: u) = ([2] : Collatz.Word) ++ u := by simp
  rw [hdecomp] at hrun
  obtain ⟨y, hhead, _⟩ := hrun.split_append
  have hreal := hhead.realizes
  have hstep :
      4 * y = 3 * Word.canonicalStart v + 1 := by
    rw [B.tail_eq]
    simpa [
      Word.Realizes,
      Word.twoSteps,
      Word.oddSteps,
      Word.affineConst
    ] using hreal
  have hs := B.coordinates.tailStart_add_one
  have hy : 2 * y = 9 * (n + d) - 1 := by
    omega
  exact ⟨y, by simpa [B.tail_eq] using hhead, hhead.end_odd, hy⟩

/-- e=2 では `q=n+d = 4*k+3`。 -/
theorem coordinateSum_eq_four_mul_add_three
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    ∃ k : ℕ, n + d = 4 * k + 3 := by
  obtain ⟨y, _hrun, hyOdd, hy⟩ := B.firstTailStep
  rcases hyOdd with ⟨a, ha⟩
  have hy' := hy
  rw [ha] at hy'
  have hqPos : 0 < n + d := by
    have hn := B.coordinates.n_pos
    have hd := B.coordinates.d_pos
    omega
  have hLinear : 9 * (n + d) = 4 * a + 3 := by
    omega
  have hq3 : 3 ≤ n + d := by
    omega
  let k := a - 2 * (n + d)
  have hkEq : n + d = 4 * k + 3 := by
    dsimp [k]
    omega
  exact ⟨k, hkEq⟩

/-- e=2 の second boundary は terminal endpoint より真に上。 -/
theorem endpoint_lt_firstTailValue
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    ∃ y : ℕ,
      Word.canonicalEnd (1 :: v) < y ∧
      2 * y = 9 * (n + d) - 1 := by
  obtain ⟨y, htail, _hyOdd, hy⟩ := B.firstTailStep
  have hhead :
      Word.Runs ([1] : Collatz.Word)
        (Word.canonicalStart (1 :: v))
        (Word.canonicalStart v) := by
    have h := B.packet.headRuns
    rw [B.packet.boundary_eq_tailStart] at h
    exact h
  have hprefix :
      Word.Runs ([1, 2] : Collatz.Word)
        (Word.canonicalStart (1 :: v)) y := by
    have happ := hhead.append htail
    simpa using happ
  have hlen :=
    B.coordinates.six_mul_n_add_two_le_tailLength B.packet
  have htailLen : 6 * n + 2 ≤ v.length := by
    simpa [Word.oddSteps] using hlen
  have hwholeLen : 2 < (1 :: v).length := by
    simp only [List.length_cons]
    omega
  have htake :
      List.take 1 v = [2] := by
    rw [B.tail_eq]
    simp
  have hprefix' :
      Word.Runs
        (1 :: List.take 1 v)
        (Word.canonicalStart (1 :: v)) y := by
    rw [htake]
    simpa using hprefix
  have hfloor :=
    B.packet.endpointFloor 2 y (by omega) hwholeLen hprefix'
  exact ⟨y, hfloor, hy⟩

/-- e=2 では endpoint floor により `d >= 3*n+3`。 -/
theorem three_mul_n_add_three_le_d
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    3 * n + 3 ≤ d := by
  obtain ⟨k, hq⟩ := B.coordinateSum_eq_four_mul_add_three
  obtain ⟨y, hTy, hy⟩ := B.endpoint_lt_firstTailValue
  have ht := B.coordinates.endpoint_add_one
  have hTailEnd := B.packet.fullEnd_eq_tailEnd
  have hTy' : Word.canonicalEnd v < y := by
    rw [← hTailEnd]
    exact hTy
  have hdGe : 3 * n ≤ d := by
    omega
  omega

/-- e=2 branch でも全 backward depth の strict-center inequality が使える。 -/
theorem backwardStrictCenter
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ v.length) :
    Word.affineConst (v.drop (v.length - r)) <
      Word.contractingGap (v.drop (v.length - r)) *
        Word.canonicalEnd (1 :: v) :=
  B.packet.tailSuffix_strictCenter hrPos hrLe

end E2BranchData

/-- 最終 `e=1` 枝を排除する局所整数論 principle。 -/
def NoE1Branch : Prop :=
  ∀ {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word},
    E1BranchData v boundary n d u → False

/-- 最終 `e=2` 枝を排除する局所整数論 principle。 -/
def NoE2Branch : Prop :=
  ∀ {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word},
    E2BranchData v boundary n d u → False

/-- endpoint-floor zero packet 自体の不存在。 -/
def NoEndpointFloorZeroPacket : Prop :=
  ∀ (v : Collatz.Word) (boundary : ℕ),
    Packet v boundary → False

/--
`NoEndpointFloorZeroPacket` は e=1/e=2 の二枝だけを排除すれば証明できる。
これが Contracting 側に露出する最終二分岐。
-/
theorem noEndpointFloorZeroPacket_of_e1_e2
    (hE1 : NoE1Branch)
    (hE2 : NoE2Branch) :
    NoEndpointFloorZeroPacket := by
  intro v boundary P
  obtain ⟨n, d, A⟩ := P.exists_coordinateData
  obtain ⟨e, u, hv, he⟩ := P.tail_head_eq_one_or_two A
  rcases he with he1 | he2
  · subst e
    exact hE1
      {
        packet := P
        coordinates := A
        tail_eq := hv
      }
  · subst e
    exact hE2
      {
        packet := P
        coordinates := A
        tail_eq := hv
      }

/--
二枝排除から natural j=0 packet の不存在を得る。
source-preserving minimal candidate と effective gap は内部で消費される。
-/
theorem noNaturalZeroReplaySignChange_of_e1_e2
    (hGap : External.TwoThreeEffectiveGapInput)
    (hE1 : NoE1Branch)
    (hE2 : NoE2Branch) :
    NoNaturalZeroReplaySignChange := by
  intro O R F D
  obtain ⟨v, boundary, P⟩ :=
    D.exists_endpointFloorZeroPacket hGap
  exact
    (noEndpointFloorZeroPacket_of_e1_e2 hE1 hE2)
      v boundary P

/-- e=1/e=2 の二枝排除だけで PositiveReturn canonical chain は消える。 -/
theorem no_canonicalChain_of_e1_e2
    (hGap : External.TwoThreeEffectiveGapInput)
    (hE1 : NoE1Branch)
    (hE2 : NoE2Branch) :
    ¬ HasCanonicalChain := by
  exact
    no_canonicalChain_of_noNaturalZeroReplaySignChange
      (noNaturalZeroReplaySignChange_of_e1_e2 hGap hE1 hE2)

end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
