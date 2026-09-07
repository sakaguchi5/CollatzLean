import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleBranchResidueBelow68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanDirectEndpointResidue

set_option linter.style.nativeDecide false

/-!
# 第3例低枝探索 3: exact certificate から `3^42 ∤ deficit` を直接得る

PureB profile numerator や Last41 を経由せず、gap-one の直接 endpoint 合同だけを使う。

もし `deficit ≡ 0 (mod 3^42)` なら、固定 target の direct endpoint 復元器が返す
canonical residue は一つに決まる。この固定 residue は偶数である。

一方、真の endpoint は

  gapOneEndpointValue m = 2*m + 1

で必ず奇数であり、range certificate により `3^42` 未満なので residue と actual integer は一致する。
従って `3^42 | deficit` は不可能である。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch

open DoubleDecomposition

/--
`deficit = 0` を右 `3^42` 復元器へ入れたときの canonical Nat representative。
固定 target だけに依存する proof-free 値。
-/
def thirdExampleZeroDeficitEndpointRepresentative : Nat := by
  letI : NeZero thirdExampleRightModulus :=
    ⟨Nat.ne_of_gt thirdExampleRightModulus_pos⟩
  exact
    (thirdExampleCleanEndpointResidueOfDeficit
      (0 : ZMod thirdExampleRightModulus)).val

/-- 上の representative は本当に zero-deficit endpoint residue を表す。 -/
theorem thirdExampleZeroDeficitEndpointRepresentative_cast :
    (thirdExampleZeroDeficitEndpointRepresentative :
        ZMod thirdExampleRightModulus) =
      thirdExampleCleanEndpointResidueOfDeficit
        (0 : ZMod thirdExampleRightModulus) := by
  native_decide

/-- canonical representative は当然 `3^42` 未満。固定計算として認証する。 -/
theorem thirdExampleZeroDeficitEndpointRepresentative_lt :
    thirdExampleZeroDeficitEndpointRepresentative <
      thirdExampleRightModulus := by
  native_decide

/-- zero-deficit から復元される固定 endpoint representative は偶数。 -/
theorem thirdExampleZeroDeficitEndpointRepresentative_even :
    thirdExampleZeroDeficitEndpointRepresentative % 2 = 0 := by
  native_decide

/--
真の exact 第3例 candidate の Ferrers deficit は `3^42` の倍数ではない。

これは `ThirdExampleProfileNumeratorNotDivisible42` とは別物であり、
ここでは certificate deficit 自身についてだけ無条件に証明する。
-/
theorem thirdExample_deficit_not_dvd_threePow42
    (R : ThirdExampleRangeCertificate)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ¬ (3 : Nat) ^ 42 ∣ deficit := by
  intro hDvd
  have hDvdM : thirdExampleRightModulus ∣ deficit := by
    simpa [thirdExampleRightModulus] using hDvd
  have hZero :
      (deficit : ZMod thirdExampleRightModulus) = 0 := by
    rcases hDvdM with ⟨t, ht⟩
    rw [ht]
    simp
  have hEndpoint :=
    thirdExampleCleanEndpointResidueOfDeficit_exact CertR C
  rw [hZero] at hEndpoint
  have hCast :
      (thirdExampleZeroDeficitEndpointRepresentative :
          ZMod thirdExampleRightModulus) =
        (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
    exact
      thirdExampleZeroDeficitEndpointRepresentative_cast.trans hEndpoint
  let : NeZero thirdExampleRightModulus :=
    ⟨Nat.ne_of_gt thirdExampleRightModulus_pos⟩
  have hVal := congrArg ZMod.val hCast
  have hEndpointLt := thirdExampleEndpoint_lt_threePow42 R C
  have hRepVal :
      (thirdExampleZeroDeficitEndpointRepresentative :
          ZMod thirdExampleRightModulus).val =
        thirdExampleZeroDeficitEndpointRepresentative := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt
      thirdExampleZeroDeficitEndpointRepresentative_lt
  have hEndpointVal :
      (gapOneEndpointValue m :
          ZMod thirdExampleRightModulus).val =
        gapOneEndpointValue m := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hEndpointLt
  have hNat :
      thirdExampleZeroDeficitEndpointRepresentative =
        gapOneEndpointValue m := by
    calc
      thirdExampleZeroDeficitEndpointRepresentative =
          (thirdExampleZeroDeficitEndpointRepresentative :
            ZMod thirdExampleRightModulus).val :=
        hRepVal.symm
      _ =
          (gapOneEndpointValue m :
            ZMod thirdExampleRightModulus).val :=
        hVal
      _ = gapOneEndpointValue m :=
        hEndpointVal
  have hEven := thirdExampleZeroDeficitEndpointRepresentative_even
  have hOdd : gapOneEndpointValue m % 2 = 1 := by
    simp [gapOneEndpointValue]
  rw [hNat] at hEven
  omega

end Collatz2.CSTMicro.ThirdExampleSearch
