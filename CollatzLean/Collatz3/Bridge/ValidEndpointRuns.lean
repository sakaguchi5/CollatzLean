import CollatzLean.Collatz3.Arithmetic.Pow23
import CollatzLean.Collatz3.Bridge.RunsToCanonical

/-!
# Collatz3 Bridge: valid endpoint equation から actual run へ

一般の `EndpointEquation -> Runs` は正しくないため置かない。
本ファイルでは exponent word が `Valid` で、endpoint が奇数である場合に限り、
endpoint affine equation から各 intermediate odd step を逆構成する。

中心定理は

`Word.Valid w`
`w.EndpointEquation x y`
`Odd y`

から

`Runs w x y`

を導く十分条件である。

これを既存の canonical lift classification と合わせることで、
非空 valid word の actual fiber 全体が

`x = canonicalStart w + oddEndpointModulus w * k`
`y = canonicalEnd w + 2 * 3^(oddSteps w) * k`

で exact に分類される。
-/

namespace Collatz3
namespace Runs

/--
valid exponent word では、endpoint affine equation と奇数 endpoint だけから
actual `Runs` を復元できる。

cons case では全体の endpoint equation から `2^e ∣ 3*x+1` を取り出す。
`2^e` と tail の `3^p` が互いに素であることが、その割り切りを head に戻す鍵になる。
-/
theorem of_valid_endpointEquation_odd
    {w : Word}
    {x y : ℕ}
    (hValid : Word.Valid w)
    (hEq : w.EndpointEquation x y)
    (hy : Odd y) :
    Runs w x y := by
  induction w generalizing x y with
  | nil =>
      have hxy : x = y :=
        (Word.endpointEquation_nil x y).1 hEq
      subst y
      exact Runs.nil x
  | cons e w ih =>
      have he : 0 < e := hValid e (by simp)
      have hTailValid : Word.Valid w := by
        intro a ha
        exact hValid a (by simp [ha])
      have hMain :=
        (Word.endpointEquation_iff (e :: w) x y).1 hEq
      have hFactor :
          2 ^ e * (2 ^ Word.twoSteps w * y) =
            3 ^ Word.oddSteps w * (3 * x + 1) +
              2 ^ e * Word.affineConst w := by
        calc
          2 ^ e * (2 ^ Word.twoSteps w * y)
              = 2 ^ (e + Word.twoSteps w) * y := by
                  rw [pow_add]
                  ring
          _ = 2 ^ Word.twoSteps (e :: w) * y := by
                  rw [Word.twoSteps_cons]
          _ =
              3 ^ Word.oddSteps (e :: w) * x +
                Word.affineConst (e :: w) := hMain
          _ =
              3 ^ Word.oddSteps w * (3 * x + 1) +
                2 ^ e * Word.affineConst w := by
                  rw [Word.oddSteps_cons, Word.affineConst_cons, pow_succ]
                  ring
      have hDvdSum :
          2 ^ e ∣
            3 ^ Word.oddSteps w * (3 * x + 1) +
              2 ^ e * Word.affineConst w := by
        rw [← hFactor]
        exact Nat.dvd_mul_right _ _
      have hDvdTranslate :
          2 ^ e ∣ 2 ^ e * Word.affineConst w :=
        Nat.dvd_mul_right _ _
      have hDvdProduct :
          2 ^ e ∣ 3 ^ Word.oddSteps w * (3 * x + 1) :=
        (Nat.dvd_add_iff_left hDvdTranslate).mpr hDvdSum
      have hCoprime :
          Nat.Coprime (2 ^ e) (3 ^ Word.oddSteps w) :=
        (Arithmetic.coprime_threePow_twoPow
          (Word.oddSteps w) e).symm
      have hDvdHead : 2 ^ e ∣ 3 * x + 1 :=
        hCoprime.dvd_of_dvd_mul_left hDvdProduct
      rcases hDvdHead with ⟨z, hz⟩
      have hCancel :
          2 ^ e * (2 ^ Word.twoSteps w * y) =
            2 ^ e *
              (3 ^ Word.oddSteps w * z + Word.affineConst w) := by
        calc
          2 ^ e * (2 ^ Word.twoSteps w * y)
              =
              3 ^ Word.oddSteps w * (3 * x + 1) +
                2 ^ e * Word.affineConst w := hFactor
          _ =
              3 ^ Word.oddSteps w * (2 ^ e * z) +
                2 ^ e * Word.affineConst w := by
                  rw [hz]
          _ =
              2 ^ e *
                (3 ^ Word.oddSteps w * z + Word.affineConst w) := by
                  ring
      have hTailMain :
          2 ^ Word.twoSteps w * y =
            3 ^ Word.oddSteps w * z + Word.affineConst w :=
        Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hCancel
      have hTailEq : Word.EndpointEquation w z y :=
        (Word.endpointEquation_iff w z y).2 hTailMain
      have hTailRun : Runs w z y :=
        ih hTailValid hTailEq hy
      have hzOdd : Odd z := by
        by_cases hw : w = []
        · subst w
          have hzy : z = y :=
            (Word.endpointEquation_nil z y).1 hTailEq
          simpa [hzy] using hy
        · exact hTailRun.start_odd_of_nonempty hw
      have hHead : OddStep e x z := by
        refine ⟨he, ?_, hzOdd⟩
        exact hz.symm
      exact Runs.cons hHead hTailRun

/--
非空 valid word では actual run と
「endpoint equation + odd endpoint」が exact に同値。
-/
theorem iff_endpointEquation_and_odd_of_valid_nonempty
    {w : Word}
    {x y : ℕ}
    (hValid : Word.Valid w)
    (hne : w ≠ []) :
    Runs w x y ↔ w.EndpointEquation x y ∧ Odd y := by
  constructor
  · intro hRun
    exact ⟨hRun.endpointEquation, hRun.end_odd_of_nonempty hne⟩
  · rintro ⟨hEq, hy⟩
    exact of_valid_endpointEquation_odd hValid hEq hy

/--
非空 valid word の actual fiber は既存 canonical lift 格子と exact に一致する。
-/
theorem iff_exists_canonicalLift_of_valid_nonempty
    {w : Word}
    {x y : ℕ}
    (hValid : Word.Valid w)
    (hne : w ≠ []) :
    Runs w x y ↔
      ∃ k : ℕ,
        x = Word.canonicalStart w + Word.oddEndpointModulus w * k ∧
        y = Word.canonicalEnd w +
          2 * (3 ^ Word.oddSteps w) * k := by
  rw [iff_endpointEquation_and_odd_of_valid_nonempty hValid hne]
  exact Word.endpointEquation_and_odd_iff_exists_lift w x y

/--
非空 valid word では canonical representative 自身が actual run を実現する。
従って canonical start は単なる affine residue representative ではなく、
実際の exponent word の最小 canonical 実現点になる。
-/
theorem canonical
    {w : Word}
    (hValid : Word.Valid w)
    (hne : w ≠ []) :
    Runs w (Word.canonicalStart w) (Word.canonicalEnd w) := by
  apply
    (iff_exists_canonicalLift_of_valid_nonempty
      (w := w)
      (x := Word.canonicalStart w)
      (y := Word.canonicalEnd w)
      hValid hne).2
  refine ⟨0, ?_, ?_⟩
  · simp
  · simp

/--
非空 valid word の canonical 格子上の任意の lift は actual run。
これが actual fiber が `ℕ` 一本であることの直接形。
-/
theorem canonicalLift
    {w : Word}
    (hValid : Word.Valid w)
    (hne : w ≠ [])
    (k : ℕ) :
    Runs w
      (Word.canonicalStart w + Word.oddEndpointModulus w * k)
      (Word.canonicalEnd w + 2 * (3 ^ Word.oddSteps w) * k) := by
  apply
    (iff_exists_canonicalLift_of_valid_nonempty
      (w := w)
      (x := Word.canonicalStart w + Word.oddEndpointModulus w * k)
      (y := Word.canonicalEnd w + 2 * (3 ^ Word.oddSteps w) * k)
      hValid hne).2
  exact ⟨k, rfl, rfl⟩

end Runs
end Collatz3
