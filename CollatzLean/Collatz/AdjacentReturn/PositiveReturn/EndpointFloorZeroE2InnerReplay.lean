import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroBranches
import CollatzLean.Collatz.Canonical.Replay
import CollatzLean.Collatz.Canonical.PrependOneCoreZeroPolynomialBound
import CollatzLean.Collatz.External.TwoThreeEffectiveGap
import CollatzLean.Collatz.Word.SuffixGapBudgetLower

/-!
# endpoint-floor E2 branch の inner replay 圧縮

E2 branch では tail が `v = 2 :: u` で始まる。
whole word `1 :: v` は FirstCrossing なので、さらに `u = 1 :: z` が強制される。

そのうえで `u` の actual run

  y -> T

を `u` の canonical replay 座標で表す。replay quotient は 0,1,2 の三値しかなく、

* quotient = 2 は effective 2-3 gap と suffix budget で矛盾
* quotient = 1 は指数的 lower bound と polynomial upper bound の trap
* quotient = 0 では double-canonical ZERO equation

へ落ちる。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero
namespace E2BranchData

/-- E2 branch の内側 suffix `u` は長さ7以上。 -/
theorem seven_le_innerLength
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    7 ≤ u.length := by
  have hlen :=
    B.coordinates.six_mul_n_add_two_le_tailLength B.packet
  have hn := B.coordinates.n_pos
  have hv : 6 * n + 2 ≤ v.length := by
    simpa [Word.oddSteps] using hlen
  rw [B.tail_eq] at hv
  simp only [List.length_cons] at hv
  omega

/-- E2 branch の inner suffix は非空。 -/
theorem inner_nonempty
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    u ≠ [] := by
  apply List.ne_nil_of_length_pos
  have h := B.seven_le_innerLength
  omega

/-- E2 branch の inner suffix は valid。 -/
theorem inner_valid
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    Word.Valid u := by
  have hv := B.packet.tail_valid
  rw [B.tail_eq] at hv
  intro e he
  exact hv e (by simp [he])

/-- E2 branch の inner suffix は all-suffix-contracting。 -/
theorem inner_allSuffixesContracting
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    Word.AllSuffixesContracting u := by
  have h := B.packet.tail_allSuffixesContracting
  rw [B.tail_eq] at h
  change
    Word.Contracting (2 :: u) ∧
      Word.AllSuffixesContracting u at h
  exact h.2

/-- E2 branch の inner suffix 自身も contracting。 -/
theorem inner_contracting
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    Word.Contracting u :=
  B.inner_allSuffixesContracting.whole B.inner_nonempty

/--
E2 の先頭 `[1,2]` の次の exponent は必ず1。
したがって whole word は `[1,2,1,...]` で始まる。
-/
theorem inner_head_eq_one
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    ∃ z : Collatz.Word, u = 1 :: z := by
  cases u with
  | nil =>
      exact False.elim (B.inner_nonempty rfl)
  | cons e z =>
      have hlen : 3 < (1 :: v).length := by
        have h7 := B.seven_le_innerLength
        rw [B.tail_eq]
        simp only [List.length_cons] at h7 ⊢
        omega
      have hExp :=
        B.packet.paradoxical.firstCrossing.properExpanding
          3 (by omega) hlen
      rw [B.tail_eq] at hExp
      have hpow : 2 ^ (3 + e) < 27 := by
        simpa [
          Word.Expanding,
          Word.twoSteps,
          Word.oddSteps,
          Nat.add_assoc,
          Nat.add_comm,
          Nat.add_left_comm
        ] using hExp
      have hePos : 0 < e := by
        have hv := B.packet.paradoxical.valid
        apply hv e
        rw [B.tail_eq]
        simp
      have heLe : e ≤ 1 := by
        by_contra hnot
        have heTwo : 2 ≤ e := by omega
        have hmono : 2 ^ 5 ≤ 2 ^ (3 + e) :=
          Nat.pow_le_pow_right
            (by omega : 0 < (2 : ℕ))
            (by omega)
        norm_num at hmono
        omega
      have he : e = 1 := by omega
      subst e
      exact ⟨z, rfl⟩

/-- inner replay の whole contracting gap。 -/
def innerGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (_B : E2BranchData v boundary n d u) : ℕ :=
  Word.contractingGap (1 :: 2 :: u)

/-- E2 branch の `sigma = m - 6*n`。 -/
def sigma
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (_B : E2BranchData v boundary n d u) : ℕ :=
  u.length - 6 * n

/-- E2 では `sigma` は正。 -/
theorem sigma_pos
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    0 < B.sigma := by
  have hlen :=
    B.coordinates.six_mul_n_add_two_le_tailLength B.packet
  have hv : 6 * n + 2 ≤ v.length := by
    simpa [Word.oddSteps] using hlen
  rw [B.tail_eq] at hv
  dsimp [sigma]
  simp only [List.length_cons] at hv
  omega

/-- `m = 6*n + sigma`。 -/
theorem innerLength_eq_six_mul_n_add_sigma
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    u.length = 6 * n + B.sigma := by
  have hs := B.sigma_pos
  dsimp [sigma] at hs ⊢
  omega

/-- whole `[1,2] ++ u` の gap の加法形。 -/
theorem innerGap_add_nine_threePow_eq_eight_twoPow
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    B.innerGap + 9 * 3 ^ u.length = 8 * 2 ^ Word.twoSteps u := by
  have hC := B.packet.paradoxical.firstCrossing.terminalContracting
  rw [B.tail_eq] at hC
  have hle :
      3 ^ Word.oddSteps (1 :: 2 :: u) ≤
        2 ^ Word.twoSteps (1 :: 2 :: u) :=
    Nat.le_of_lt hC
  have hgap :
      3 ^ Word.oddSteps (1 :: 2 :: u) +
          Word.contractingGap (1 :: 2 :: u) =
        2 ^ Word.twoSteps (1 :: 2 :: u) := by
    unfold Word.contractingGap
    exact Nat.add_sub_of_le hle
  dsimp [innerGap]
  calc
    Word.contractingGap (1 :: 2 :: u) +
        9 * 3 ^ u.length
        =
      3 ^ u.length * 9 +
        Word.contractingGap (1 :: 2 :: u) := by
          ring
    _ =
      2 ^ Word.twoSteps u * 8 := by
        have hgap' := hgap
        simp [
          Word.oddSteps,
          Word.twoSteps,
          pow_add
        ] at hgap'
        ring_nf at hgap' ⊢
        exact hgap'
    _ =
      8 * 2 ^ Word.twoSteps u := by
        ring

/-- E2 inner whole gap は正。 -/
theorem innerGap_pos
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    0 < B.innerGap := by
  have hC := B.packet.paradoxical.firstCrossing.terminalContracting
  rw [B.tail_eq] at hC
  dsimp [innerGap]
  exact hC.contractingGap_pos

/-- inner canonical start は正。 -/
theorem innerCanonicalStart_pos
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    0 < Word.canonicalStart u := by
  have hrun := B.inner_valid.canonicalRuns
  have hodd := hrun.start_odd (Word.canonicalEnd_odd u)
  rcases hodd with ⟨k, hk⟩
  omega

/--
E2 で `[2]` の後から terminal までを走る inner actual run。
-/
theorem innerRuns
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    ∃ y : ℕ,
      Word.Runs u y (Word.canonicalEnd (1 :: v)) ∧
      4 * y = 3 * Word.canonicalStart v + 1 ∧
      2 * y = 9 * (n + d) - 1 := by
  have hrun :
      Word.Runs v
        (Word.canonicalStart v)
        (Word.canonicalEnd v) :=
    B.packet.tail_valid.canonicalRuns
  rw [B.tail_eq] at hrun
  have hdecomp : (2 :: u) = ([2] : Collatz.Word) ++ u := by simp
  rw [hdecomp] at hrun
  obtain ⟨y, hhead, hsuffix⟩ := hrun.split_append
  have hstep :
      4 * y = 3 * Word.canonicalStart v + 1 := by
    have hreal := hhead.realizes
    simpa [
      B.tail_eq,
      Word.Realizes,
      Word.twoSteps,
      Word.oddSteps,
      Word.affineConst
    ] using hreal
  have hs := B.coordinates.tailStart_add_one
  have htwo :
      2 * y = 9 * (n + d) - 1 := by
    omega
  have hsuffix' :
      Word.Runs u y (Word.canonicalEnd v) := by
    simpa [B.tail_eq] using hsuffix
  have hend := B.packet.fullEnd_eq_tailEnd
  have hsuffixFull :
      Word.Runs u y (Word.canonicalEnd (1 :: v)) := by
    rw [hend]
    exact hsuffix'
  exact ⟨y, hsuffixFull, hstep, htwo⟩

/--
inner actual run を canonical replay 座標化した packet。
-/
structure InnerReplayData
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) : Type where
  y : ℕ
  runs : Word.Runs u y (Word.canonicalEnd (1 :: v))
  four_y_eq : 4 * y = 3 * Word.canonicalStart v + 1
  two_y_eq : 2 * y = 9 * (n + d) - 1
  coordinate :
    Word.ReplayCoordinate u y (Word.canonicalEnd (1 :: v))
  quotient_le_two : coordinate.quotient ≤ 2

/-- inner replay data は必ず存在。 -/
noncomputable def innerReplayData
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    InnerReplayData B := by
  classical
  let y : ℕ := Nat.find B.innerRuns
  have hy :
      Word.Runs u y (Word.canonicalEnd (1 :: v)) ∧
      4 * y = 3 * Word.canonicalStart v + 1 ∧
      2 * y = 9 * (n + d) - 1 := by
    exact Nat.find_spec B.innerRuns
  have hrun :
      Word.Runs u y (Word.canonicalEnd (1 :: v)) :=
    hy.1
  have hfour :
      4 * y = 3 * Word.canonicalStart v + 1 :=
    hy.2.1
  have htwo :
      2 * y = 9 * (n + d) - 1 :=
    hy.2.2
  let C :
      Word.ReplayCoordinate u y (Word.canonicalEnd (1 :: v)) :=
    Word.ReplayCoordinate.ofRuns hrun B.inner_nonempty
  have hsLt :
      Word.canonicalStart v <
        8 * 2 ^ Word.twoSteps u := by
    rw [B.tail_eq]
    have h :=
      Word.canonicalStart_lt_modulus (2 :: u)
    calc
      Word.canonicalStart (2 :: u)
          < Word.residueModulus (2 :: u) := h
      _ = 2 ^ Word.twoSteps u * 8 := by
        simp [
          Word.residueModulus,
          Word.twoSteps,
          pow_add
        ]
        ring
      _ = 8 * 2 ^ Word.twoSteps u := by
        ring
  have hyLe :
      y ≤ 6 * 2 ^ Word.twoSteps u := by
    nlinarith [hfour, hsLt]
  have hstartPos :
      0 < Word.canonicalStart u :=
    B.innerCanonicalStart_pos
  have hmodulus :
      Word.residueModulus u =
        2 * 2 ^ Word.twoSteps u := by
    simp only [Word.residueModulus, pow_succ]
    ring
  have hqLe : C.quotient ≤ 2 := by
    by_contra hnot
    have hqThree : 3 ≤ C.quotient := by
      omega
    have hmul :
        3 * Word.residueModulus u ≤
          Word.residueModulus u * C.quotient := by
      have h :=
        Nat.mul_le_mul_left
          (Word.residueModulus u) hqThree
      simpa [Nat.mul_comm] using h
    have hstart := C.start_eq
    rw [hmodulus] at hmul hstart
    nlinarith
  exact {
    y := y
    runs := hrun
    four_y_eq := hfour
    two_y_eq := htwo
    coordinate := C
    quotient_le_two := hqLe
  }

/-- inner replay quotient は 0,1,2 の三値。 -/
theorem InnerReplayData.quotient_cases
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (I : InnerReplayData B) :
    I.coordinate.quotient = 0 ∨
      I.coordinate.quotient = 1 ∨
      I.coordinate.quotient = 2 := by
  have hq : I.coordinate.quotient ≤ 2 :=
    I.quotient_le_two
  omega
/--
inner replay の exact defect balance。

`G = contractingGap([1,2] ++ u)` とすると

  9*canonicalEnd(u) + 5
    = 8*canonicalStart(u) + 18*n + 2*G*j.
-/
theorem innerReplay_balance
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B) :
    9 * Word.canonicalEnd u + 5 =
      8 * Word.canonicalStart u +
        18 * n + 2 * B.innerGap * I.coordinate.quotient := by
  have hstart := I.coordinate.start_eq
  have hfinish := I.coordinate.finish_eq
  have htailEnd := B.packet.fullEnd_eq_tailEnd
  have hend := B.coordinates.endpoint_add_one
  have hgap := B.innerGap_add_nine_threePow_eq_eight_twoPow
  have hmodulus :
      Word.residueModulus u = 2 * 2 ^ Word.twoSteps u := by
    simp [Word.residueModulus, pow_succ]
    ring
  rw [hmodulus] at hstart
  have hn : 0 < n :=
    B.coordinates.n_pos
  have hd : 0 < d :=
    B.coordinates.d_pos
  have hTplus :
      Word.canonicalEnd (1 :: v) + 1 =
        6 * n + 4 * d := by
    rw [htailEnd]
    exact hend
  have hyplus :
      2 * I.y + 1 =
        9 * (n + d) := by
    have h := I.two_y_eq
    omega
  have hbase :
      9 * Word.canonicalEnd (1 :: v) + 5 =
        8 * I.y + 18 * n := by
    omega
  rw [hfinish] at hbase
  have hgapQ :
      2 * B.innerGap * I.coordinate.quotient +
          18 * 3 ^ u.length * I.coordinate.quotient =
        16 * 2 ^ Word.twoSteps u * I.coordinate.quotient := by
    calc
      2 * B.innerGap * I.coordinate.quotient +
          18 * 3 ^ u.length * I.coordinate.quotient
          =
        2 * (B.innerGap + 9 * 3 ^ u.length) *
          I.coordinate.quotient := by
            ring
      _ =
        2 * (8 * 2 ^ Word.twoSteps u) *
          I.coordinate.quotient := by
            rw [hgap]
      _ =
        16 * 2 ^ Word.twoSteps u *
          I.coordinate.quotient := by
            ring
  simp only [Word.oddSteps] at hbase
  nlinarith [hbase, hstart, hgapQ]

/--
E2 inner suffix の defect は `3*m` より小さい。
subtraction-free 形で

  9*end + 6 < 8*start + 3*m

と記録する。
-/
theorem innerDefect_lt_three_mul_length
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    9 * Word.canonicalEnd u + 6 <
      8 * Word.canonicalStart u + 3 * u.length := by
  have hAll := B.inner_allSuffixesContracting
  have hlen : 7 ≤ u.length := B.seven_le_innerLength
  have hBudgetLower :
      2 * 2 ^ Word.twoSteps u < Word.suffixGapBudget u := by
    exact
      hAll.two_mul_twoPow_lt_suffixGapBudget_of_seven_le_length
        hlen
  have hBudgetEq :=
    Word.AllSuffixesContracting.oddSteps_mul_twoPow_eq_three_mul_affine_add_suffixGapBudget
      hAll
  have hBudget :
      u.length * 2 ^ Word.twoSteps u =
        3 * Word.affineConst u + Word.suffixGapBudget u := by
    simpa [Word.oddSteps] using hBudgetEq
  have hReal := Word.canonicalEnd_realizes u
  have hReal' :
      2 ^ Word.twoSteps u * Word.canonicalEnd u =
        3 ^ u.length * Word.canonicalStart u +
          Word.affineConst u := by
    simpa [Word.Realizes, Word.oddSteps] using hReal
  have hGap := B.innerGap_add_nine_threePow_eq_eight_twoPow
  have hApos : 0 < 2 ^ Word.twoSteps u :=
    Nat.pow_pos (by omega)
  have hGapNonneg :
      9 * 3 ^ u.length ≤ 8 * 2 ^ Word.twoSteps u := by
    omega
  have hScaled :
      2 ^ Word.twoSteps u *
          (9 * Word.canonicalEnd u + 6) <
        2 ^ Word.twoSteps u *
          (8 * Word.canonicalStart u + 3 * u.length) := by
    nlinarith [hBudgetLower, hBudget, hReal', hGapNonneg]
  exact (Nat.mul_lt_mul_left hApos).1 (by
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.add_mul] using hScaled)

/-- effective gap から inner whole gap は少なくとも `m+2`。 -/
theorem innerGap_ge_length_add_two
    (hGap : External.TwoThreeEffectiveGapInput)
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    u.length + 2 ≤ B.innerGap := by
  have hC := B.packet.paradoxical.firstCrossing.terminalContracting
  rw [B.tail_eq] at hC
  have h :=
    External.twoThreeGap_ge_exponent hGap hC
  dsimp [innerGap]
  simpa [
    Word.contractingGap,
    Word.oddSteps,
    Word.twoSteps,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using h

/-- inner replay quotient `2` は完全排除。 -/
theorem no_innerReplay_two
    (hGap : External.TwoThreeEffectiveGapInput)
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 2) :
    False := by
  have hbal := B.innerReplay_balance I
  rw [hq] at hbal
  have hupp := B.innerDefect_lt_three_mul_length
  have hG := B.innerGap_ge_length_add_two hGap
  have hn := B.coordinates.n_pos
  nlinarith

/--
inner replay quotient `1` では inner length は `18*n+5` より大きい。
-/
theorem innerReplay_one_length_lower
    (hGap : External.TwoThreeEffectiveGapInput)
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 1) :
    18 * n + 5 < u.length := by
  have hbal := B.innerReplay_balance I
  rw [hq] at hbal
  have hupp := B.innerDefect_lt_three_mul_length
  have hG := B.innerGap_ge_length_add_two hGap
  nlinarith

/--
inner replay quotient `1` では coordinate sum は `3^m` に対して指数的に大きい。
-/
theorem innerReplay_one_exponential_lower
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 1) :
    4 * 3 ^ u.length < 9 * (n + d) := by
  have hstart := I.coordinate.start_eq
  rw [hq] at hstart
  have hmodulus :
      Word.residueModulus u = 2 * 2 ^ Word.twoSteps u := by
    simp [Word.residueModulus, pow_succ]
    ring
  rw [hmodulus] at hstart
  have hstartPos := B.innerCanonicalStart_pos
  have hy :
      2 * I.y = 9 * (n + d) - 1 :=
    I.two_y_eq
  have hqPos : 0 < n + d := by
    have hn := B.coordinates.n_pos
    omega
  have hyPlus :
      2 * I.y + 1 = 9 * (n + d) := by
    omega
  have hyLower :
      2 * 2 ^ Word.twoSteps u < I.y := by
    rw [hstart]
    omega
  have hA :
      4 * 2 ^ Word.twoSteps u < 9 * (n + d) := by
    omega
  have hC : 3 ^ u.length < 2 ^ Word.twoSteps u := by
    simpa [Word.Contracting, Word.oddSteps] using B.inner_contracting
  nlinarith

/--
inner replay quotient `1` の exponential-vs-polynomial trap。
固定 Baker constants に対し、同じ packet が

* `4*3^m < 9*(n+d)`
* canonical start の polynomial upper bound

を同時に満たす。
-/
theorem innerReplay_one_exponential_polynomial_trap
    (hEffective : External.TwoThreeEffectiveGapInput)
    (hPoly : External.TwoThreeGapPolynomialBound)
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 1) :
    ∃ K A : ℕ,
      0 < K ∧
      18 * n + 5 < u.length ∧
      4 * 3 ^ u.length < 9 * (n + d) ∧
      3 * (4 * (n + d) - 1) <
        (u.length + 2) *
          (K * (u.length + 3) ^ A + 1) := by
  have hlen := B.innerReplay_one_length_lower hEffective I hq
  have hexp := B.innerReplay_one_exponential_lower I hq
  obtain ⟨K, A, n0, hK, _hn0, _hreturn, _hexact, _hsix, hpoly0⟩ :=
    B.packet.paradoxical.polynomialCanonicalStartBound hPoly
  have hStart := B.coordinates.fullStart_add_one
  have hStartEq :
      Word.canonicalStart (1 :: v) = 4 * (n + d) - 1 := by
    omega
  have hOdd :
      Word.oddSteps (1 :: v) = u.length + 2 := by
    rw [B.tail_eq]
    simp [Word.oddSteps]
  have hpoly :
      3 * (4 * (n + d) - 1) <
        (u.length + 2) *
          (K * (u.length + 3) ^ A + 1) := by
    rw [hStartEq, hOdd] at hpoly0
    have hsub :
        (u.length + 2 - 6 * n0) ≤ u.length + 2 :=
      Nat.sub_le _ _
    have hmul :=
      Nat.mul_le_mul_right
        (K * (u.length + 3) ^ A + 1)
        hsub
    exact lt_of_lt_of_le hpoly0 (by
      simpa [Nat.mul_comm] using hmul)
  exact ⟨K, A, hK, hlen, hexp, hpoly⟩

/-- quotient `0` なら inner actual start/end は canonical start/end。 -/
theorem innerReplay_zero_doubleCanonical
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 0) :
    I.y = Word.canonicalStart u ∧
      Word.canonicalEnd (1 :: v) = Word.canonicalEnd u := by
  constructor
  · exact I.coordinate.start_eq_canonical_of_quotient_eq_zero hq
  · rw [I.coordinate.finish_eq, hq]
    simp

/--
quotient `0` の ZERO exact equation。

`E = suffixGapBudget u`, `A = 2^twoSteps(u)`, `sigma = m-6*n` とすると

innerGap * canonicalStart(u) + 3*E
= (3*sigma + 5) * A.
-/
theorem innerReplay_zero_sigma_budget_balance
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 0) :
    B.innerGap * Word.canonicalStart u +
        3 * Word.suffixGapBudget u =
      (3 * B.sigma + 5) * 2 ^ Word.twoSteps u := by
  have hbal := B.innerReplay_balance I
  rw [hq] at hbal
  simp only [mul_zero, add_zero] at hbal
  have hReal := Word.canonicalEnd_realizes u
  have hReal' :
      2 ^ Word.twoSteps u * Word.canonicalEnd u =
        3 ^ u.length * Word.canonicalStart u +
          Word.affineConst u := by
    simpa [Word.Realizes, Word.oddSteps] using hReal
  have hBudgetEq :=
    Word.AllSuffixesContracting.oddSteps_mul_twoPow_eq_three_mul_affine_add_suffixGapBudget
      B.inner_allSuffixesContracting
  have hBudget :
      u.length * 2 ^ Word.twoSteps u =
        3 * Word.affineConst u +
          Word.suffixGapBudget u := by
    simpa [Word.oddSteps] using hBudgetEq
  have hGap :=
    B.innerGap_add_nine_threePow_eq_eight_twoPow
  have hlen :=
    B.innerLength_eq_six_mul_n_add_sigma
  have hGapS :=
    congrArg
      (fun t : ℕ => t * Word.canonicalStart u)
      hGap
  have hReal9 :=
    congrArg
      (fun t : ℕ => 9 * t)
      hReal'
  have hBudget3 :=
    congrArg
      (fun t : ℕ => 3 * t)
      hBudget
  have hBalA :=
    congrArg
      (fun t : ℕ => t * 2 ^ Word.twoSteps u)
      hbal
  have hLenA :=
    congrArg
      (fun t : ℕ =>
        3 * t * 2 ^ Word.twoSteps u)
      hlen
  ring_nf at hGapS hReal9 hBudget3 hBalA hLenA ⊢
  nlinarith

/-- quotient `0` では budget は ZERO equation の上側に制約される。 -/
theorem innerReplay_zero_budget_strict_upper
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 0) :
    3 * Word.suffixGapBudget u <
      (3 * B.sigma + 5) * 2 ^ Word.twoSteps u := by
  have hEq := B.innerReplay_zero_sigma_budget_balance I hq
  have hG := B.innerGap_pos
  have hs := B.innerCanonicalStart_pos
  have hprod : 0 < B.innerGap * Word.canonicalStart u :=
    Nat.mul_pos hG hs
  nlinarith

end E2BranchData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
