import CollatzLean.Collatz.Canonical.PrependOneCoreBranches

/-!
# prepend-one CORE の quotient zero obstruction

`j = 0` の CORE failure を、canonical first crossing における
smallest-first paradoxical exact obstruction として切り出す。

ここでいう smallest-first は odd-only boundary に関する主張である。
proper prefix の各 actual odd boundary は canonical start より真に大きく、
CORE failure により terminal canonical end も canonical start より真に大きい。

さらに canonical start/end はともに奇数なので、terminal return gap は `2*n`
と書け、contracting gap を用いた exact affine balance を得る。
-/

namespace Collatz
namespace Word

/--
canonical first crossing が smallest-first paradoxical であることを、
exact return equation と合わせて保持する pure finite-word obstruction。
-/
structure SmallestFirstParadoxicalExactObstruction
    (w : Collatz.Word) : Prop where
  valid : w.Valid
  firstCrossing : w.FirstCrossing
  allSuffixesContracting : w.AllSuffixesContracting
  positiveReturn : w.canonicalStart < w.canonicalEnd
  properBoundaryAboveStart :
    ∀ (m y : ℕ),
      0 < m →
      m < w.length →
      Runs (w.take m) w.canonicalStart y →
        w.canonicalStart < y
  exactReturn :
    ∃ n : ℕ,
      0 < n ∧
      w.canonicalEnd = w.canonicalStart + 2 * n ∧
      w.affineConst =
        w.contractingGap * w.canonicalStart +
          2 ^ (w.twoSteps + 1) * n

/--
prepend-one quotient zero failure に固有の replay 情報を、
smallest-first paradoxical obstruction と一緒に保持する packet。
-/
structure PrependOneZeroFailureObstruction
    (v : Collatz.Word) (boundary : ℕ) : Prop where
  tail_nonempty : v ≠ []
  replay : PrependOneReplayData v boundary 0
  coreFailure : ¬ PrependOneCoreCondition v 0
  boundary_eq : boundary = v.canonicalStart
  suffixStart_mod_three : v.canonicalStart % 3 = 2
  fullEnd_eq_suffixEnd :
    canonicalEnd (1 :: v) = v.canonicalEnd
  paradoxical :
    SmallestFirstParadoxicalExactObstruction (1 :: v)

/-- quotient zero では replay boundary は suffix canonical start そのもの。 -/
theorem PrependOneReplayData.zero_boundary_eq_canonicalStart
    {v : Collatz.Word} {boundary : ℕ}
    (D : PrependOneReplayData v boundary 0) :
    boundary = v.canonicalStart := by
  simpa using D.boundary_eq

/-- quotient zero では full endpoint は suffix canonical end そのもの。 -/
theorem PrependOneReplayData.zero_fullEnd_eq_suffixEnd
    {v : Collatz.Word} {boundary : ℕ}
    (D : PrependOneReplayData v boundary 0) :
    canonicalEnd (1 :: v) = v.canonicalEnd := by
  simpa using D.endpoint_eq

/--
first crossing の canonical start から proper prefix を actual に走らせた
任意の odd boundary は canonical start より真に大きい。
-/
theorem FirstCrossing.canonicalStart_lt_properPrefixBoundary
    {w : Collatz.Word}
    (hvalid : w.Valid)
    (hF : w.FirstCrossing)
    {m y : ℕ}
    (hmPos : 0 < m)
    (hmLt : m < w.length)
    (hrun : Runs (w.take m) w.canonicalStart y) :
    w.canonicalStart < y := by
  have hExp :
      Expanding (w.take m) :=
    hF.properExpanding m hmPos hmLt
  have hReal := hrun.realizes
  have hStartOdd : Odd w.canonicalStart := by
    exact
      hvalid.canonicalRuns.start_odd
        (canonicalEnd_odd w)
  have hStartPos : 0 < w.canonicalStart := by
    rcases hStartOdd with ⟨a, ha⟩
    omega
  change
    2 ^ Word.twoSteps (w.take m) <
      3 ^ Word.oddSteps (w.take m) at hExp
  change
    2 ^ Word.twoSteps (w.take m) * y =
      3 ^ Word.oddSteps (w.take m) * w.canonicalStart +
        Word.affineConst (w.take m) at hReal
  by_contra hnot
  have hyLe :
      y ≤ w.canonicalStart := by
    omega
  have hscaled :
      2 ^ Word.twoSteps (w.take m) * y ≤
        2 ^ Word.twoSteps (w.take m) * w.canonicalStart := by
    exact
      Nat.mul_le_mul_left
        (2 ^ Word.twoSteps (w.take m))
        hyLe
  have hstrict :
      2 ^ Word.twoSteps (w.take m) * w.canonicalStart <
        3 ^ Word.oddSteps (w.take m) * w.canonicalStart := by
    exact
      (Nat.mul_lt_mul_right hStartPos).2 hExp
  have hrhs :
      3 ^ Word.oddSteps (w.take m) * w.canonicalStart ≤
        3 ^ Word.oddSteps (w.take m) * w.canonicalStart +
          Word.affineConst (w.take m) := by
    omega
  have hlt :
      2 ^ Word.twoSteps (w.take m) * y <
        3 ^ Word.oddSteps (w.take m) * w.canonicalStart +
          Word.affineConst (w.take m) := by
    exact
      lt_of_le_of_lt
        hscaled
        (lt_of_lt_of_le hstrict hrhs)
  omega

/--
valid contracting canonical word が positive return なら、
奇数性により return gap は正の `2*n` であり、
その `n` は contracting gap を用いた exact equation を満たす。
-/
theorem canonicalPositiveReturn_exactObstruction
    {w : Collatz.Word}
    (hvalid : w.Valid)
    (hC : w.Contracting)
    (hpos : w.canonicalStart < w.canonicalEnd) :
    ∃ n : ℕ,
      0 < n ∧
      w.canonicalEnd = w.canonicalStart + 2 * n ∧
      w.affineConst =
        w.contractingGap * w.canonicalStart +
          2 ^ (w.twoSteps + 1) * n := by
  have hStartOdd : Odd w.canonicalStart := by
    exact hvalid.canonicalRuns.start_odd (canonicalEnd_odd w)
  have hEndOdd : Odd w.canonicalEnd :=
    canonicalEnd_odd w
  rcases hStartOdd with ⟨a, ha⟩
  rcases hEndOdd with ⟨b, hb⟩
  have hab : a < b := by
    omega
  let n := b - a
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  have hreturn :
      w.canonicalEnd = w.canonicalStart + 2 * n := by
    dsimp [n]
    omega
  have hReal := canonicalEnd_realizes w
  unfold Realizes at hReal
  have hgap :
      3 ^ w.oddSteps + w.contractingGap =
        2 ^ w.twoSteps := by
    unfold Contracting at hC
    unfold contractingGap
    omega
  have hgapMul :
      3 ^ w.oddSteps * w.canonicalStart +
          w.contractingGap * w.canonicalStart =
        2 ^ w.twoSteps * w.canonicalStart := by
    calc
      3 ^ w.oddSteps * w.canonicalStart +
          w.contractingGap * w.canonicalStart
          = (3 ^ w.oddSteps + w.contractingGap) *
              w.canonicalStart := by ring
      _ = 2 ^ w.twoSteps * w.canonicalStart := by rw [hgap]
  have hexact :
      w.affineConst =
        w.contractingGap * w.canonicalStart +
          2 ^ (w.twoSteps + 1) * n := by
    have hsum :
        3 ^ w.oddSteps * w.canonicalStart +
            (w.contractingGap * w.canonicalStart +
              2 ^ (w.twoSteps + 1) * n) =
          3 ^ w.oddSteps * w.canonicalStart +
            w.affineConst := by
      calc
        3 ^ w.oddSteps * w.canonicalStart +
            (w.contractingGap * w.canonicalStart +
              2 ^ (w.twoSteps + 1) * n)
            =
          (3 ^ w.oddSteps * w.canonicalStart +
            w.contractingGap * w.canonicalStart) +
              2 ^ (w.twoSteps + 1) * n := by ring
        _ =
          2 ^ w.twoSteps * w.canonicalStart +
            2 ^ (w.twoSteps + 1) * n := by rw [hgapMul]
        _ =
          2 ^ w.twoSteps *
            (w.canonicalStart + 2 * n) := by
              rw [pow_succ]
              ring
        _ = 2 ^ w.twoSteps * w.canonicalEnd := by
              rw [← hreturn]
        _ =
          3 ^ w.oddSteps * w.canonicalStart +
            w.affineConst := hReal
    exact (Nat.add_left_cancel hsum).symm
  exact ⟨n, hnPos, hreturn, hexact⟩

/--
quotient zero の CORE failure は full canonical run の positive return と同値方向を持つ。
ここでは failure から strict positive return を取り出す。
-/
theorem PrependOneReplayData.zero_coreFailure_positiveReturn
    {v : Collatz.Word} {boundary : ℕ}
    (D : PrependOneReplayData v boundary 0)
    (hFail : ¬ PrependOneCoreCondition v 0) :
    canonicalStart (1 :: v) < canonicalEnd (1 :: v) := by
  have hboundary : boundary = v.canonicalStart :=
    D.zero_boundary_eq_canonicalStart
  have hendpoint :
      canonicalEnd (1 :: v) = v.canonicalEnd :=
    D.zero_fullEnd_eq_suffixEnd
  have hhead := D.headStep
  rw [hboundary] at hhead
  unfold PrependOneCoreCondition at hFail
  have hCoreLt :
      3 * v.canonicalStart <
        v.canonicalStart + 1 + 3 * v.canonicalEnd := by
    omega
  have hStartEnd :
      canonicalStart (1 :: v) < v.canonicalEnd := by
    omega
  rw [hendpoint]
  exact hStartEnd

/--
`j = 0` CORE failure を smallest-first paradoxical exact obstruction へ完全変換する。

この theorem 以後、zero branch の未解決数学は
`SmallestFirstParadoxicalExactObstruction (1 :: v)` の不存在として扱える。
-/
theorem prependOneZeroFailure_to_smallestFirstParadoxicalExactObstruction
    {v : Collatz.Word} {boundary : ℕ}
    (hvne : v ≠ [])
    (hvalid : Word.Valid (1 :: v))
    (hF : Word.FirstCrossing (1 :: v))
    (D : PrependOneReplayData v boundary 0)
    (hFail : ¬ PrependOneCoreCondition v 0) :
    PrependOneZeroFailureObstruction v boundary := by
  have hpos :
      canonicalStart (1 :: v) < canonicalEnd (1 :: v) :=
    D.zero_coreFailure_positiveReturn hFail
  have hexact :=
    canonicalPositiveReturn_exactObstruction
      hvalid hF.terminalContracting hpos
  have hproper :
      ∀ (m y : ℕ),
        0 < m →
        m < (1 :: v).length →
        Word.Runs
          (List.take m (1 :: v))
          (Word.canonicalStart (1 :: v))
          y →
        Word.canonicalStart (1 :: v) < y := by
    intro m y hmPos hmLt hrun
    exact hF.canonicalStart_lt_properPrefixBoundary
      hvalid hmPos hmLt hrun
  refine
    {
      tail_nonempty := hvne
      replay := D
      coreFailure := hFail
      boundary_eq := D.zero_boundary_eq_canonicalStart
      suffixStart_mod_three := D.zero_canonicalStart_mod_three
      fullEnd_eq_suffixEnd := D.zero_fullEnd_eq_suffixEnd
      paradoxical := ?_
    }
  exact
    {
      valid := hvalid
      firstCrossing := hF
      allSuffixesContracting := hF.allSuffixesContracting
      positiveReturn := hpos
      properBoundaryAboveStart := hproper
      exactReturn := hexact
    }

/--
method-style wrapper。first crossing data から quotient zero failure obstruction を得る。
-/
theorem FirstCrossing.zeroReplay_coreFailure_obstruction
    {v : Collatz.Word} {boundary : ℕ}
    (hF : Word.FirstCrossing (1 :: v))
    (hvne : v ≠ [])
    (hvalid : Word.Valid (1 :: v))
    (D : PrependOneReplayData v boundary 0)
    (hFail : ¬ PrependOneCoreCondition v 0) :
    PrependOneZeroFailureObstruction v boundary :=
  prependOneZeroFailure_to_smallestFirstParadoxicalExactObstruction
    hvne hvalid hF D hFail

end Word
end Collatz
