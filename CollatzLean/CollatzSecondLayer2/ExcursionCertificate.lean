import CollatzLean.CollatzSecondLayer2.CaptureNormalization
import CollatzLean.CollatzSecondLayer2.FirstCrossing


/-!
# large excursion certificate

実軌道上の一つの有限区間について、すべての非空prefixが膨張することを
整数冪不等式だけで保存する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 実軌道上の全prefix膨張block。 -/
structure LargeExcursionCertificate
    (O : OddOrbit) (anchor totalLength : ℕ) where
  blockOffset : ℕ
  blockLength : ℕ
  length_pos : 0 < blockLength
  inside : blockOffset + blockLength ≤ totalLength
  allPrefixesExpanding : ∀ m : ℕ,
    0 < m → m ≤ blockLength →
    Expanding (O.segmentWord (anchor + blockOffset) m)

namespace LargeExcursionCertificate

/-- certificate全体のblockも膨張する。 -/
theorem expanding
    {O : OddOrbit} {anchor totalLength : ℕ}
    (C : LargeExcursionCertificate O anchor totalLength) :
    Expanding
      (O.segmentWord (anchor + C.blockOffset) C.blockLength) :=
  C.allPrefixesExpanding C.blockLength C.length_pos le_rfl

/-- first-crossingのproper prefixから標準large excursionを得る。 -/
def ofFirstCrossing
    {O : OddOrbit} {anchor p : ℕ}
    (hC : FirstCrossingAt O anchor p)
    (hp : 1 < p) :
    LargeExcursionCertificate O anchor p where
  blockOffset := 0
  blockLength := p - 1
  length_pos := by omega
  inside := by omega
  allPrefixesExpanding := by
    intro m hm hmlen
    have hmp : m < p := by omega
    have hE :=
      hC.properExpanding m hm (by
        simpa using hmp)
    have htake := O.segmentWord_take_of_le
      (i := anchor) (m := m) (n := p) (Nat.le_of_lt hmp)
    rw [htake] at hE
    exact hE

/--
first-crossing内部のcertificateを、同じfuture-minimum anchorから始まる
proper prefixへ固定する。
-/
def lockToCrossingAnchor
    {O : OddOrbit} {anchor p : ℕ}
    (hC : FirstCrossingAt O anchor p)
    (C : LargeExcursionCertificate O anchor p)
    (hspan : 1 < C.blockOffset + C.blockLength) :
    LargeExcursionCertificate O anchor p where
  blockOffset := 0
  blockLength := C.blockOffset + C.blockLength - 1

  length_pos := by
    omega

  inside := by
    have hsub :
        C.blockOffset + C.blockLength - 1 ≤
          C.blockOffset + C.blockLength :=
      Nat.sub_le _ _
    have hins :
        C.blockOffset + C.blockLength ≤ p :=
      C.inside
    simpa using le_trans hsub hins

  allPrefixesExpanding := by
    intro m hm hmlen
    have hins :
        C.blockOffset + C.blockLength ≤ p :=
      C.inside
    have hmp : m < p := by
      omega
    have hmword :
        m < (O.segmentWord anchor p).length := by
      simpa using hmp
    have hE :=
      hC.properExpanding m hm hmword
    have htake :=
      O.segmentWord_take_of_le
        (i := anchor)
        (m := m)
        (n := p)
        (Nat.le_of_lt hmp)
    rw [htake] at hE
    exact hE

end LargeExcursionCertificate
end CollatzSecondLayer2
