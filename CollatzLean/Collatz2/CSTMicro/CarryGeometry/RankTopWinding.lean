import CollatzLean.Collatz2.CSTMicro.CarryGeometry.UniversalCutWeight
import Mathlib.Data.Nat.ModEq

/-!
# Rank-top winding

universal cut weight を ordinary representative `0,...,G-1` に持ち上げ、

  S(w) = sum_k X_k.val

を定義する。
actual first-failure upper では

  S = 3 q + n G

となる。sharp strip `3q < m` と各 weight の positivity から

  1 <= n < m

を得る。
-/

namespace Collatz2
namespace Word

/-- universal cut weight の ordinary representative。 -/
noncomputable def rankTopRepresentative
    {w : Word}
    (hF : FirstCrossing w)
    (k : ℕ) : ℕ :=
  (universalCutWeight hF k).val

/-- final rank top representatives の ordinary integer sum。 -/
noncomputable def rankTopSum
    {w : Word}
    (hF : FirstCrossing w) : ℕ :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k => rankTopRepresentative hF k)

/-- ordinary representative sum を mod G に戻すと universal weight sum。 -/
theorem FirstCrossing.rankTopSum_cast_eq_universalCutWeightSum
    {w : Word}
    (hF : FirstCrossing w) :
    ((rankTopSum hF : ℕ) : ZMod (terminalGap w)) =
      universalCutWeightSum hF := by
  have hContract :
      3 ^ oddSteps w < 2 ^ twoSteps w :=
    (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
  have hGapPos : 0 < terminalGap w := by
    unfold terminalGap
    omega
  letI : NeZero (terminalGap w) :=
    ⟨Nat.ne_of_gt hGapPos⟩
  unfold rankTopSum universalCutWeightSum
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  unfold rankTopRepresentative
  exact ZMod.natCast_zmod_val _

/-- terminal gap が nontrivial なら各 rank-top representative は正。 -/
theorem FirstCrossing.rankTopRepresentative_pos
    {w : Word}
    (hF : FirstCrossing w)
    (hGap : 1 < terminalGap w)
    (k : ℕ) :
    0 < rankTopRepresentative hF k := by
  unfold rankTopRepresentative
  exact (ZMod.val_pos).2 (hF.universalCutWeight_ne_zero hGap k)

/-- 各 positive representative を足すので `m <= S`。 -/
theorem FirstCrossing.oddSteps_le_rankTopSum
    {w : Word}
    (hF : FirstCrossing w)
    (hGap : 1 < terminalGap w) :
    oddSteps w ≤ rankTopSum hF := by
  calc
    oddSteps w =
        Finset.sum (Finset.range (oddSteps w)) (fun _ => 1) := by simp
    _ ≤
        Finset.sum (Finset.range (oddSteps w))
          (fun k => rankTopRepresentative hF k) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hF.rankTopRepresentative_pos hGap k
    _ = rankTopSum hF := by rfl

/-- 各 representative は `G-1` 以下なので `S < mG`。 -/
theorem FirstCrossing.rankTopSum_lt_oddSteps_mul_gap
    {w : Word}
    (hF : FirstCrossing w)
    (hGap : 1 < terminalGap w) :
    rankTopSum hF < oddSteps w * terminalGap w := by
  let G := terminalGap w
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  have hGPos : 0 < G := by
    dsimp [G]
    omega
  haveI : NeZero G := ⟨Nat.ne_of_gt hGPos⟩
  have hLe :
      rankTopSum hF ≤ oddSteps w * (G - 1) := by
    unfold rankTopSum
    calc
      Finset.sum (Finset.range (oddSteps w))
          (fun k => rankTopRepresentative hF k)
          ≤
        Finset.sum (Finset.range (oddSteps w))
          (fun _ => G - 1) := by
            apply Finset.sum_le_sum
            intro k hk
            have hlt : rankTopRepresentative hF k < G := by
              unfold rankTopRepresentative
              exact ZMod.val_lt _
            omega
      _ = oddSteps w * (G - 1) := by simp
  have hGapLt : G - 1 < G := by omega
  have hMulLt :
      oddSteps w * (G - 1) < oddSteps w * G :=
    (Nat.mul_lt_mul_left hpPos).2 hGapLt
  exact lt_of_le_of_lt hLe hMulLt

end Word

namespace CSTMicro
namespace FirstFailureEdge

/-- first-failure bounded Farey residue `0<D<G` から terminal gap > 1。 -/
theorem one_lt_upperExponentWord_terminalGap
    (F : FirstFailureEdge) :
    1 < Collatz2.Word.terminalGap F.upperExponentWord := by
  let D := F.toFirstFailureFareyData
  have hDPos := D.residue_pos
  have hDLt := D.residue_lt_gap
  have hGInt : (1 : ℤ) < D.farey.G := by omega
  have hEncoded := F.upperExponentWord_terminalGap
  have hEdgeGap := F.step.edge.wordTerminalGap_eq
  have hFarey := D.farey_G_eq_wordTerminalGap
  have hCast :
      (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) =
        D.farey.G := by
    calc
      (Collatz2.Word.terminalGap F.upperExponentWord : ℤ)
          = (wordTerminalGap F.step.edge.upperWord : ℤ) := by
              exact_mod_cast hEncoded
      _ = (wordTerminalGap F.step.edge.lowerWord : ℤ) := by
              exact_mod_cast hEdgeGap.symm
      _ = D.farey.G := hFarey.symm
  have h :
      (1 : ℤ) <
        (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) := by
    rw [hCast]
    exact hGInt
  exact_mod_cast h

/-- rank-top ordinary sum も `3q` と同じ residue class。 -/
theorem rankTopSum_cast_eq_three_mul_upperNormalizedDefectNat
    (F : FirstFailureEdge) :
    ((Collatz2.Word.rankTopSum F.upperExponentWord_firstCrossing : ℕ) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) =
      (((3 * F.upperNormalizedDefectNat : ℕ)) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
  let hF := F.upperExponentWord_firstCrossing
  calc
    ((Collatz2.Word.rankTopSum hF : ℕ) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord))
        = Collatz2.Word.universalCutWeightSum hF :=
          hF.rankTopSum_cast_eq_universalCutWeightSum
    _ =
      (3 : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        ((F.upperNormalizedDefectNat : ℕ) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
            simpa [hF] using
              F.universalCutWeightSum_eq_three_mul_upperNormalizedDefectNat
    _ =
      (((3 * F.upperNormalizedDefectNat : ℕ)) :
        ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
          push_cast
          ring

/--
nontrivial first-failure upper の rank-top winding normal form。

  rankTopSum = 3*q + n*G,
  1 <= n < m.
-/
theorem exists_rankTopWinding
    (F : FirstFailureEdge)
    (hLen : 2 < F.step.edge.upperWord.length) :
    ∃ n : ℕ,
      1 ≤ n ∧
      n < Collatz2.Word.oddSteps F.upperExponentWord ∧
      Collatz2.Word.rankTopSum F.upperExponentWord_firstCrossing =
        3 * F.upperNormalizedDefectNat +
          Collatz2.Word.terminalGap F.upperExponentWord * n := by
  let w := F.upperExponentWord
  let hF : Collatz2.Word.FirstCrossing w := F.upperExponentWord_firstCrossing
  let p := Collatz2.Word.oddSteps w
  let G := Collatz2.Word.terminalGap w
  let q := F.upperNormalizedDefectNat
  let S := Collatz2.Word.rankTopSum hF
  have hGap : 1 < G := by
    simpa [G, w] using F.one_lt_upperExponentWord_terminalGap
  have hSharp : 3 * q < p := by
    simpa [q, p, w] using
      F.three_mul_upperNormalizedDefectNat_lt_oddSteps hLen
  have hLower : p ≤ S := by
    simpa [p, S] using hF.oddSteps_le_rankTopSum hGap
  have hStrict : 3 * q < S := lt_of_lt_of_le hSharp hLower
  have hUpper : S < p * G := by
    simpa [S, p, G] using hF.rankTopSum_lt_oddSteps_mul_gap hGap
  have hCast :
      ((S : ℕ) : ZMod G) = (((3 * q : ℕ)) : ZMod G) := by
    simpa [S, q, G, w, hF] using
      F.rankTopSum_cast_eq_three_mul_upperNormalizedDefectNat
  have hMod : S ≡ 3 * q [MOD G] :=
    (ZMod.natCast_eq_natCast_iff S (3 * q) G).1 hCast
  have hMod' : 3 * q ≡ S [MOD G] := hMod.symm
  have hLe : 3 * q ≤ S := Nat.le_of_lt hStrict
  obtain ⟨n, hEq⟩ :=
    (Nat.modEq_iff_exists_eq_add hLe).1 hMod'
  have hnPos : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := by omega
    rw [hn0] at hEq
    simp at hEq
    omega
  have hnLt : n < p := by
    by_contra hnot
    have hpn : p ≤ n := by omega
    have hGp : G * p ≤ G * n := Nat.mul_le_mul_left G hpn
    have hGn : G * n ≤ S := by
      rw [hEq]
      omega
    have hpGS : p * G ≤ S := by
      simpa [Nat.mul_comm] using le_trans hGp hGn
    omega
  refine ⟨n, ?_, ?_, ?_⟩
  · omega
  · simpa [p, w] using hnLt
  · simpa [S, q, G, w, hF, Nat.mul_comm] using hEq

end FirstFailureEdge
end CSTMicro
end Collatz2
