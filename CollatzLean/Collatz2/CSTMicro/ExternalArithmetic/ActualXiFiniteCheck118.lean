import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryAFromRhin

set_option linter.style.nativeDecide false
set_option linter.style.emptyLine false
set_option exponentiation.threshold 4096


/-!
# Actual critical Xi: finite small-residue exclusion on 118 <= e < 1538

既存 strong Xi engine は precision `e >= 1538` を排除する。
このファイルではその直前の有限範囲

  118 <= e < 1538

を exact native arithmetic で埋める。

重要な点は proof-oriented `beattyIndex = Nat.find ...` を native evaluator に
直接渡さないこと。代わりに、各 endpoint odd count `m` に対して

  beta_m = beattyIndex m
  Phi_(m+1) = 3 Phi_m + 2^beta_m

を一回前向きに更新する scalar state を使う。

state の residue

  - Phi_m * 3^(-m)  (mod 2^beta_m)

は exact に `criticalXiTruncationClass beta_m m` である。

native scan は `m = 0,...,970` を一度だけ走査し、
`118 <= beta_m < 1538` の state について

  boundaryFailureResidueBound rhinGapK rhinGapA beta_m
    < Xi(beta_m,m).val

を確認する。

`beattyIndex 971 = 1538` も同じ verified state から得るため、
任意の `e < 1538` candidate はこの finite scan の範囲へ必ず入る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. executable Beatty / Phi state -/

/--
endpoint odd count `m` に対応する executable state。

* `beta = beattyIndex m`
* `phi` は `3^m * beattyInverseContribution e m` を任意 precision `e`
  で表す integer numerator

を invariant とする。
-/
private structure Xi118ScanState where
  m : ℕ
  beta : ℕ
  phi : ℕ
deriving Inhabited

private def xi118ScanInitial : Xi118ScanState := {
  m := 0
  beta := 0
  phi := 0
}

/--
`beta_m` から `beta_(m+1)` を power inequality だけで executable に更新する。

Beatty increment は常に 1 または 2。
-/
private def Xi118ScanState.nextBeta
    (S : Xi118ScanState) : ℕ :=
  if 3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2) then
    S.beta + 1
  else
    S.beta + 2

/--
一 odd endpoint だけ進める。

`Phi_(m+1) = 3 Phi_m + 2^beta_m`.
-/
private def Xi118ScanState.next
    (S : Xi118ScanState) : Xi118ScanState := {
  m := S.m + 1
  beta := S.nextBeta
  phi := 3 * S.phi + 2 ^ S.beta
}

/--
state が表す Xi class。
-/
private def Xi118ScanState.residueClass
    (S : Xi118ScanState) : ZMod (2 ^ S.beta) :=
  (-(S.phi : ZMod (2 ^ S.beta))) *
    invThreePow S.beta S.m

private def Xi118ScanState.residue
    (S : Xi118ScanState) : ℕ :=
  S.residueClass.val

/--
proof-oriented object との semantic invariant。
-/
private def Xi118ScanState.Correct
    (S : Xi118ScanState) : Prop :=
  S.beta = beattyIndex S.m ∧
    ∀ e : ℕ,
      (S.phi : ZMod (2 ^ e)) =
        (3 : ZMod (2 ^ e)) ^ S.m *
          beattyInverseContribution e S.m

private theorem xi118ScanInitial_correct :
    xi118ScanInitial.Correct := by
  constructor
  · simp [xi118ScanInitial]
  · intro e
    simp only [xi118ScanInitial, Nat.cast_zero, pow_zero, beattyInverseContribution_zero, mul_zero]

/--
correct state の executable Beatty update は proof-oriented `beattyIndex`
の次値と exact に一致する。
-/
private theorem Xi118ScanState.nextBeta_eq
    {S : Xi118ScanState}
    (hS : S.Correct) :
    S.nextBeta = beattyIndex (S.m + 1) := by
  have hBeta : S.beta = beattyIndex S.m := hS.1

  have hStrict0 := beattyIndex_lt_succ S.m
  have hStrict :
      S.beta < beattyIndex (S.m + 1) := by
    simpa [hBeta] using hStrict0
  have hLower :
      S.beta + 1 ≤ beattyIndex (S.m + 1) := by
    omega

  have hUpperM := beattyIndex_upper S.m
  rw [← hBeta] at hUpperM
  have hCandidate :
      3 ^ (S.m + 1) ≤ 2 ^ ((S.beta + 2) + 1) := by
    rw [pow_succ]
    calc
      3 ^ S.m * 3
          ≤ 2 ^ (S.beta + 1) * 3 :=
        Nat.mul_le_mul_right 3 hUpperM
      _ ≤ 2 ^ (S.beta + 1) * 4 := by
        exact
          Nat.mul_le_mul_left
            (2 ^ (S.beta + 1))
            (by norm_num : 3 ≤ 4)
      _ = 2 ^ ((S.beta + 2) + 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  have hUpper :
      beattyIndex (S.m + 1) ≤ S.beta + 2 :=
    beattyIndex_le_of_upper hCandidate

  by_cases hOne :
      3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2)
  · have hAtOne :
        beattyIndex (S.m + 1) ≤ S.beta + 1 := by
      apply beattyIndex_le_of_upper
      simpa [Nat.add_assoc] using hOne
    have hEq :
        beattyIndex (S.m + 1) = S.beta + 1 := by
      omega
    simp [Xi118ScanState.nextBeta, hOne, hEq]
  · have hNe :
        beattyIndex (S.m + 1) ≠ S.beta + 1 := by
      intro hEq
      have hU := beattyIndex_upper (S.m + 1)
      rw [hEq] at hU
      apply hOne
      simpa [Nat.add_assoc] using hU
    have hEq :
        beattyIndex (S.m + 1) = S.beta + 2 := by
      omega
    simp [Xi118ScanState.nextBeta, hOne, hEq]

/--
state invariant は一 step で保存される。
-/
private theorem Xi118ScanState.next_correct
    {S : Xi118ScanState}
    (hS : S.Correct) :
    S.next.Correct := by
  constructor
  · exact S.nextBeta_eq hS
  · intro e
    have hPhi := hS.2 e
    have hInv :=
      threePow_mul_invThreePow e (S.m + 1)
    have hTerm :
        (3 : ZMod (2 ^ e)) ^ (S.m + 1) *
            ((2 : ZMod (2 ^ e)) ^ beattyIndex S.m *
              invThreePow e (S.m + 1)) =
          (2 : ZMod (2 ^ e)) ^ beattyIndex S.m := by
      calc
        (3 : ZMod (2 ^ e)) ^ (S.m + 1) *
              ((2 : ZMod (2 ^ e)) ^ beattyIndex S.m *
                invThreePow e (S.m + 1))
            =
          (2 : ZMod (2 ^ e)) ^ beattyIndex S.m *
            ((3 : ZMod (2 ^ e)) ^ (S.m + 1) *
              invThreePow e (S.m + 1)) := by
                ring
        _ = (2 : ZMod (2 ^ e)) ^ beattyIndex S.m := by
              rw [hInv]
              ring
    change
      ((3 * S.phi + 2 ^ S.beta : ℕ) : ZMod (2 ^ e)) =
        (3 : ZMod (2 ^ e)) ^ (S.m + 1) *
          beattyInverseContribution e (S.m + 1)
    push_cast
    rw [beattyInverseContribution_succ, mul_add, hTerm]
    rw [hPhi, hS.1, pow_succ]
    ring

/--
correct state の scalar residue は exact Xi truncation class。
-/
private theorem Xi118ScanState.residueClass_eq_xi
    {S : Xi118ScanState}
    (hS : S.Correct) :
    S.residueClass =
      criticalXiTruncationClass S.beta S.m := by
  have hPhi := hS.2 S.beta
  have hInv :=
    threePow_mul_invThreePow S.beta S.m
  unfold Xi118ScanState.residueClass
  unfold criticalXiTruncationClass
  rw [hPhi]
  calc
    (-((
        (3 : ZMod (2 ^ S.beta)) ^ S.m *
          beattyInverseContribution S.beta S.m))) *
        invThreePow S.beta S.m
        =
      - beattyInverseContribution S.beta S.m *
        ((3 : ZMod (2 ^ S.beta)) ^ S.m *
          invThreePow S.beta S.m) := by
            ring
    _ = - beattyInverseContribution S.beta S.m := by
          rw [hInv]
          ring

private theorem Xi118ScanState.residue_eq_xi
    {S : Xi118ScanState}
    (hS : S.Correct) :
    S.residue =
      (criticalXiTruncationClass S.beta S.m).val := by
  exact congrArg ZMod.val (S.residueClass_eq_xi hS)

/-! ## 2. one-pass finite scanner -/

/--
relevant precision だけを検査する Bool。
-/
private def Xi118ScanState.good
    (S : Xi118ScanState) : Bool :=
  if 118 ≤ S.beta ∧ S.beta < 1538 then
    decide
      (boundaryFailureResidueBound
          rhinGapK rhinGapA S.beta <
        S.residue)
  else
    true

private def xi118FiniteScan :
    ℕ → Xi118ScanState → Bool
  | 0, _S =>
      true
  | fuel + 1, S =>
      S.good &&
        xi118FiniteScan fuel S.next

private def xi118StateAt :
    ℕ → Xi118ScanState
  | 0 =>
      xi118ScanInitial
  | n + 1 =>
      (xi118StateAt n).next

@[simp] private theorem xi118StateAt_m
    (n : ℕ) :
    (xi118StateAt n).m = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [xi118StateAt, Xi118ScanState.next, ih]

private theorem xi118StateAt_correct
    (n : ℕ) :
    (xi118StateAt n).Correct := by
  induction n with
  | zero =>
      exact xi118ScanInitial_correct
  | succ n ih =>
      exact Xi118ScanState.next_correct ih

/--
一 step 以上の scan が true なら head と tail がともに true。
-/
private theorem xi118FiniteScan_succ_true
    (fuel : ℕ)
    (S : Xi118ScanState)
    (h :
      xi118FiniteScan (fuel + 1) S = true) :
    S.good = true ∧
      xi118FiniteScan fuel S.next = true := by
  simpa [xi118FiniteScan] using h

/--
scan が true の区間では state ごとの `good` がすべて true。
-/
private theorem xi118FiniteScan_sound :
    ∀ fuel n : ℕ,
      xi118FiniteScan fuel (xi118StateAt n) = true →
      ∀ k : ℕ,
        n ≤ k →
        k < n + fuel →
        (xi118StateAt k).good = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro n _hScan k _hnk hk
      omega
  | succ fuel ih =>
      intro n hScan k hnk hk
      have hSplit :=
        xi118FiniteScan_succ_true
          fuel (xi118StateAt n) hScan
      rcases hSplit with ⟨hHead, hTail⟩
      by_cases hkn : k = n
      · subst k
        exact hHead
      · have hTail' :
            xi118FiniteScan fuel
              (xi118StateAt (n + 1)) = true := by
          simpa [xi118StateAt] using hTail
        exact
          ih
            (n + 1)
            hTail'
            k
            (by omega)
            (by omega)

/--
`m=0,...,970` の一回前向き scan。
-/
private def xi118FullCheck : Bool :=
  xi118FiniteScan 971 xi118ScanInitial

/--
frozen exact finite computation。
-/
private theorem xi118FullCheck_ok :
    xi118FullCheck = true := by
  native_decide

private theorem xi118StateAt_good_of_lt
    {m : ℕ}
    (hm : m < 971) :
    (xi118StateAt m).good = true := by
  have hScan :
      xi118FiniteScan 971 (xi118StateAt 0) = true := by
    simpa [xi118FullCheck, xi118StateAt] using
      xi118FullCheck_ok
  exact
    xi118FiniteScan_sound
      971 0 hScan m (by omega) (by omega)

/--
971 step 後の executable scanner の beta 値。
-/
private theorem xi118StateAt_971_beta :
    (xi118StateAt 971).beta = 1538 := by
    native_decide

/--
scanner 自身から `beattyIndex 971 = 1538` を certified する。
-/
theorem beattyIndex_971_eq_1538 :
    beattyIndex 971 = 1538 := by
  have hCorrect := xi118StateAt_correct 971
  have hBeta :
      (xi118StateAt 971).beta = beattyIndex 971 := by
    have h := hCorrect.1
    rw [xi118StateAt_m 971] at h
    exact h
  calc
    beattyIndex 971
        = (xi118StateAt 971).beta :=
      hBeta.symm
    _ = 1538 :=
      xi118StateAt_971_beta

/-! ## 3. public finite Xi exclusion datum -/

/--
finite range `118 <= e < 1538` では critical Xi residue 自身が
Rhin polynomial bound より strictly 大きい。

これは arbitrary candidate `x` の排除へ使う public arithmetic theorem。
-/
theorem criticalXiResidue_gt_boundaryFailureBound_of_118_le_lt_1538
    {e m : ℕ}
    (h118 : 118 ≤ e)
    (h1538 : e < 1538)
    (hem : e = beattyIndex m) :
    boundaryFailureResidueBound rhinGapK rhinGapA e <
      (criticalXiTruncationClass e m).val := by
  have hmLt : m < 971 := by
    by_contra hnot
    have hmGe : 971 ≤ m := by
      omega
    by_cases hmEq : m = 971
    · subst m
      rw [beattyIndex_971_eq_1538] at hem
      omega
    · have hmStrict : 971 < m := by
        omega
      have hMono :=
        beattyIndex_strictMono hmStrict
      rw [beattyIndex_971_eq_1538] at hMono
      rw [← hem] at hMono
      omega

  let S := xi118StateAt m
  have hCorrect : S.Correct := by
    simpa [S] using xi118StateAt_correct m
  have hBeta : S.beta = e := by
    calc
      S.beta = beattyIndex S.m := hCorrect.1
      _ = beattyIndex m := by
        rw [show S.m = m by simp [S]]
      _ = e := hem.symm

  have hGood0 :
      (xi118StateAt m).good = true :=
    xi118StateAt_good_of_lt hmLt
  have hGood : S.good = true := by
    simpa [S] using hGood0

  have hRange :
      118 ≤ S.beta ∧ S.beta < 1538 := by
    rw [hBeta]
    exact ⟨h118, h1538⟩

  have hIneq :
      boundaryFailureResidueBound
          rhinGapK rhinGapA S.beta <
        S.residue := by
    unfold Xi118ScanState.good at hGood
    rw [ite_eq_left hRange] at hGood
    exact of_decide_eq_true hGood

  have hResidue :=
    Xi118ScanState.residue_eq_xi hCorrect
  have hSm : S.m = m := by
    simp [S]

  rw [hBeta, hSm] at hResidue
  rw [hBeta, hResidue] at hIneq
  exact hIneq

end ExternalArithmetic
end CSTMicro
end Collatz2
