import CollatzLean.Collatz.FiniteOrbit.Reconstruction
import CollatzLean.Collatz.Canonical.Replay

/-!
# canonical cylinderのactual復元とdigit分解

valid有限語のcanonical affine解をactual odd runへ復元する。
さらに語を右へ延長したとき、canonical startの変化を
旧prefixのcanonical modulusを基数とする明示digitで表す。
-/

namespace Collatz
namespace Word

/-- valid語のcanonical start/endはactual odd runをなす。 -/
theorem Valid.canonicalRuns
    {w : Collatz.Word} (hvalid : w.Valid) :
    Runs w w.canonicalStart w.canonicalEnd := by
  exact hvalid.runs_of_realizes
    w.canonicalEnd_realizes
    w.canonicalEnd_odd

/-- 右延長語のcanonical startを旧prefix modulusで割ったquotient。 -/
def extensionDigit (u v : Collatz.Word) : ℕ :=
  (u ++ v).canonicalStart / u.residueModulus

/--
非空valid prefixを右へ延長すると、延長後canonical startは
旧canonical startと同じ旧modulus剰余を持つ。
-/
theorem canonicalStart_append_mod
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    (u ++ v).canonicalStart % u.residueModulus = u.canonicalStart := by
  have hrun :
      Runs (u ++ v) (u ++ v).canonicalStart (u ++ v).canonicalEnd :=
    hvalid.canonicalRuns
  obtain ⟨y, hprefix, _hsuffix⟩ := hrun.split_append
  have hy : Odd y := hprefix.end_odd_of_ne_nil hu
  exact hprefix.realizes.start_mod_eq_canonicalStart hy

/--
canonical cylinder digitによる右延長startの完全分解。
`next = current + modulus * digit`。
-/
theorem canonicalStart_append_eq
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    (u ++ v).canonicalStart =
      u.canonicalStart + u.residueModulus * u.extensionDigit v := by
  have hmod := canonicalStart_append_mod hvalid hu
  have hdecomp := Nat.mod_add_div (u ++ v).canonicalStart u.residueModulus
  rw [hmod] at hdecomp
  unfold extensionDigit
  simpa [Nat.mul_comm] using hdecomp.symm

/-- 一文字`e`の右延長ではcylinder digitは`2^e`未満。 -/
theorem extensionDigit_singleton_lt_twoPow
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    u.extensionDigit [e] < 2 ^ e := by
  have hmodulus :
      (u ++ [e]).residueModulus = u.residueModulus * 2 ^ e := by
    simp [residueModulus, pow_add, Nat.add_comm,
      Nat.add_left_comm, Nat.mul_comm]
  have hstartLt :
      (u ++ [e]).canonicalStart < u.residueModulus * 2 ^ e := by
    rw [← hmodulus]
    exact canonicalStart_lt_modulus (u ++ [e])
  have hdecomp := canonicalStart_append_eq hvalid hu
  by_contra hnot
  have hdigit : 2 ^ e ≤ u.extensionDigit [e] :=
    Nat.le_of_not_gt hnot
  have hmul :
      u.residueModulus * 2 ^ e ≤
        u.residueModulus * u.extensionDigit [e] :=
    Nat.mul_le_mul_left u.residueModulus hdigit
  have hmulLe :
      u.residueModulus * u.extensionDigit [e] ≤
        (u ++ [e]).canonicalStart := by
    rw [hdecomp]
    omega
  omega

/-- 右延長canonical runの旧prefix終端に現れる明示境界値。 -/
def canonicalPrefixBoundary (u v : Collatz.Word) : ℕ :=
  u.canonicalEnd + 2 * 3 ^ u.oddSteps * u.extensionDigit v

/--
右延長canonical runを旧prefixで切った実際の境界値は、
canonical endをcylinder digitだけreplayした値に一致する。
-/
theorem canonicalPrefixBoundary_eq
    {u v : Collatz.Word} {y : ℕ}
    (hu : u ≠ [])
    (hprefix : Runs u (u ++ v).canonicalStart y) :
    y = u.canonicalPrefixBoundary v := by
  let C : ReplayCoordinate u (u ++ v).canonicalStart y :=
    ReplayCoordinate.ofRuns hprefix hu
  have hq : C.quotient = u.extensionDigit v := by
    rfl
  rw [C.finish_eq, hq]
  rfl

/-- 延長canonical runは明示canonical prefix boundaryで正確に分割できる。 -/
theorem canonicalRuns_append_split_at_boundary
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    Runs u (u ++ v).canonicalStart (u.canonicalPrefixBoundary v) ∧
      Runs v (u.canonicalPrefixBoundary v) (u ++ v).canonicalEnd := by
  have hrun :
      Runs (u ++ v) (u ++ v).canonicalStart (u ++ v).canonicalEnd :=
    hvalid.canonicalRuns
  obtain ⟨y, hprefix, hsuffix⟩ := hrun.split_append
  have hy : y = u.canonicalPrefixBoundary v :=
    canonicalPrefixBoundary_eq hu hprefix
  subst y
  exact ⟨hprefix, hsuffix⟩

/-- 一般の右suffixでもcylinder digitは`2^(suffix twoSteps)`未満。 -/
theorem extensionDigit_general_lt
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    u.extensionDigit v < 2 ^ v.twoSteps := by
  have hmodulus :
      (u ++ v).residueModulus =
        u.residueModulus * 2 ^ v.twoSteps := by
    simp [residueModulus, twoSteps_append, pow_add]
    ac_rfl
  have hstartLt :
      (u ++ v).canonicalStart <
        u.residueModulus * 2 ^ v.twoSteps := by
    rw [← hmodulus]
    exact canonicalStart_lt_modulus (u ++ v)
  have hdecomp := canonicalStart_append_eq hvalid hu
  by_contra hnot
  have hdigit : 2 ^ v.twoSteps ≤ u.extensionDigit v :=
    Nat.le_of_not_gt hnot
  have hmul :
      u.residueModulus * 2 ^ v.twoSteps ≤
        u.residueModulus * u.extensionDigit v :=
    Nat.mul_le_mul_left u.residueModulus hdigit
  have hmulLe :
      u.residueModulus * u.extensionDigit v ≤
        (u ++ v).canonicalStart := by
    rw [hdecomp]
    omega
  omega

/-- digitが0であることと、actual prefix boundaryが旧canonical endに一致することは同値。 -/
theorem extensionDigit_zero_iff_boundary_canonical
    (u v : Collatz.Word) :
    u.extensionDigit v = 0 ↔
      u.canonicalPrefixBoundary v = u.canonicalEnd := by
  constructor
  · intro hzero
    simp [canonicalPrefixBoundary, hzero]
  · intro hboundary
    unfold canonicalPrefixBoundary at hboundary
    have hmul :
        2 * 3 ^ u.oddSteps * u.extensionDigit v = 0 := by
      omega
    rcases Nat.mul_eq_zero.mp hmul with hfactor | hdigit
    · have hfactorPos : 0 < 2 * 3 ^ u.oddSteps :=
        Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
      omega
    · exact hdigit

/--
一つのcylinder digitが表す全natural replay layerはactual runとして存在する。
各layerの開始・終了は延長canonical runの対応境界以下にある。
-/
theorem extensionDigit_replayFamily
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ []) :
    ∀ j : ℕ, j ≤ u.extensionDigit v →
      Runs u
          (u.canonicalStart + u.residueModulus * j)
          (u.canonicalEnd + 2 * 3 ^ u.oddSteps * j) ∧
        u.canonicalStart + u.residueModulus * j ≤
          (u ++ v).canonicalStart ∧
        u.canonicalEnd + 2 * 3 ^ u.oddSteps * j ≤
          u.canonicalPrefixBoundary v := by
  intro j hj
  have huvalid : u.Valid := by
    intro a ha
    exact hvalid a (by simp [ha])
  have hrun := huvalid.canonicalRuns.replay (k := j)
  have hrun' :
      Runs u
        (u.canonicalStart + u.residueModulus * j)
        (u.canonicalEnd + 2 * 3 ^ u.oddSteps * j) := by
    simpa [residueModulus] using hrun
  have hstartEq := canonicalStart_append_eq hvalid hu
  have hstartMul :
      u.residueModulus * j ≤
        u.residueModulus * u.extensionDigit v :=
    Nat.mul_le_mul_left u.residueModulus hj
  have hstartLe :
      u.canonicalStart + u.residueModulus * j ≤
        (u ++ v).canonicalStart := by
    rw [hstartEq]
    omega
  have hfinishMul :
      (2 * 3 ^ u.oddSteps) * j ≤
        (2 * 3 ^ u.oddSteps) * u.extensionDigit v :=
    Nat.mul_le_mul_left (2 * 3 ^ u.oddSteps) hj
  have hfinishLe :
      u.canonicalEnd + 2 * 3 ^ u.oddSteps * j ≤
        u.canonicalPrefixBoundary v := by
    unfold canonicalPrefixBoundary
    omega
  exact ⟨hrun', hstartLe, hfinishLe⟩

/-- 二つのcanonical cylinderが同じsigned shadowを持つことの自然数版。 -/
def CanonicalShadowPreserved (u w : Collatz.Word) : Prop :=
  w.canonicalStart + u.residueModulus =
    u.canonicalStart + w.residueModulus

/-- 一文字延長のmodulusは旧modulusの`2^e`倍。 -/
private theorem residueModulus_append_singleton_eq
    (u : Collatz.Word) (e : ℕ) :
    (u ++ [e]).residueModulus = u.residueModulus * 2 ^ e := by
  simp [residueModulus, pow_add, Nat.add_comm,
    Nat.add_left_comm, Nat.mul_comm]

/--
一文字延長ではdigitが最大値`2^e-1`であることと、
`canonicalStart - residueModulus`というsigned shadowの保存が同値。
-/
theorem extensionDigit_maximal_iff_shadow_preserved
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    u.extensionDigit [e] = 2 ^ e - 1 ↔
      CanonicalShadowPreserved u (u ++ [e]) := by
  have hstart := canonicalStart_append_eq hvalid hu
  have hmodulus := residueModulus_append_singleton_eq u e
  have hmodulusPos : 0 < u.residueModulus := by
    simp [residueModulus]
  have hpowPos : 0 < 2 ^ e := Nat.pow_pos (by omega)
  constructor
  · intro hmax
    have hplus : u.extensionDigit [e] + 1 = 2 ^ e := by
      omega
    unfold CanonicalShadowPreserved
    rw [hstart, hmodulus]
    calc
      u.canonicalStart + u.residueModulus * u.extensionDigit [e] +
            u.residueModulus
          = u.canonicalStart +
              u.residueModulus * (u.extensionDigit [e] + 1) := by ring
      _ = u.canonicalStart + u.residueModulus * 2 ^ e := by rw [hplus]
  · intro hshadow
    unfold CanonicalShadowPreserved at hshadow
    rw [hstart, hmodulus] at hshadow
    have hcancel :
        u.residueModulus * u.extensionDigit [e] + u.residueModulus =
          u.residueModulus * 2 ^ e := by
      omega
    have hmul :
        u.residueModulus * (u.extensionDigit [e] + 1) =
          u.residueModulus * 2 ^ e := by
      calc
        u.residueModulus * (u.extensionDigit [e] + 1)
            = u.residueModulus * u.extensionDigit [e] +
                u.residueModulus := by ring
        _ = u.residueModulus * 2 ^ e := hcancel
    have hplus : u.extensionDigit [e] + 1 = 2 ^ e :=
      Nat.mul_left_cancel hmodulusPos hmul
    omega

/-- 一文字cylinder digitの三分類。 -/
inductive CylinderDigitOutcome (u : Collatz.Word) (e : ℕ) : Type
  | zero
      (digit_eq : u.extensionDigit [e] = 0)
  | intermediate
      (digit_pos : 0 < u.extensionDigit [e])
      (digit_lt_max : u.extensionDigit [e] < 2 ^ e - 1)
  | maximal
      (digit_eq : u.extensionDigit [e] = 2 ^ e - 1)

/-- validな非空prefixの一文字延長digitをzero/intermediate/maximalへ完全分類する。 -/
def classifyCylinderDigit
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    CylinderDigitOutcome u e := by
  have he : 0 < e := hvalid e (by simp)
  have hbound : u.extensionDigit [e] < 2 ^ e :=
    extensionDigit_singleton_lt_twoPow hvalid hu
  have hpowTwo : 2 ≤ 2 ^ e := by
    obtain ⟨r, hr⟩ : ∃ r : ℕ, e = r + 1 :=
      ⟨e - 1, by omega⟩
    rw [hr, pow_succ]
    have hpos : 0 < 2 ^ r := Nat.pow_pos (by omega)
    omega
  by_cases hzero : u.extensionDigit [e] = 0
  · exact CylinderDigitOutcome.zero hzero
  · by_cases hmax : u.extensionDigit [e] = 2 ^ e - 1
    · exact CylinderDigitOutcome.maximal hmax
    · exact CylinderDigitOutcome.intermediate (by omega) (by omega)

end Word
end Collatz
