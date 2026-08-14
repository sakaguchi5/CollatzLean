import CollatzLean.Collatz2.Canonical.Replay

/-!
# Collatz2 Canonical: endpoint fundamental interval

canonical start の基本区間

  canonicalStart w < 2 * 2^H

に対する endpoint 側の dual bound

  canonicalEnd w < 2 * 3^p

を証明する。

証明の要点は、一文字 head の後の tail run を tail 自身の replay coordinate で読むこと。
full canonical start が start modulus 未満なので、tail replay quotient は高々2であり、
帰納的な endpoint bound と合わせると endpoint は `2*3^p` 未満に収まる。
-/

namespace Collatz2
namespace Word

/--
canonical run の先頭 step の直後の値は、
tail 側 fundamental interval の3倍未満に入る。

具体的には `y < 6 * 2^H`。
-/
theorem canonicalFirstTailStart_lt_six_mul_twoPow
    {e : ℕ} {v : Word} {y : ℕ}
    (hstep :
      2 ^ e * y =
        3 * canonicalStart (e :: v) + 1) :
    y < 6 * 2 ^ twoSteps v := by
  have hstartLt :
      canonicalStart (e :: v) <
        residueModulus (e :: v) :=
    canonicalStart_lt_modulus (e :: v)
  have hpre :
      3 * canonicalStart (e :: v) + 1 <
        3 * residueModulus (e :: v) := by
    omega
  have hscaled :
      2 ^ e * y <
        2 ^ e * (6 * 2 ^ twoSteps v) := by
    calc
      2 ^ e * y
          = 3 * canonicalStart (e :: v) + 1 := hstep
      _ < 3 * residueModulus (e :: v) := hpre
      _ = 2 ^ e * (6 * 2 ^ twoSteps v) := by
          simp [residueModulus, twoSteps, pow_add, pow_succ]
          ring
  have hpowPos : 0 < 2 ^ e :=
    Nat.pow_pos (by omega)
  exact
    (Nat.mul_lt_mul_left hpowPos).mp hscaled

/--
replay start が `6 * 2^H` 未満なら、
replay quotient は高々2。

quotient が3以上なら start は
`3 * residueModulus = 6 * 2^H`
以上になって矛盾する。
-/
theorem ReplayCoordinate.quotient_le_two_of_start_lt_six_mul_twoPow
    {v : Word} {X Y : ℕ}
    (R : ReplayCoordinate v X Y)
    (hX :
      X < 6 * 2 ^ twoSteps v) :
    R.quotient ≤ 2 := by
  by_contra hnot
  have hqThree : 3 ≤ R.quotient := by
    omega
  have hmul :
      residueModulus v * 3 ≤
        residueModulus v * R.quotient :=
    Nat.mul_le_mul_left
      (residueModulus v) hqThree
  have hXLower :
      residueModulus v * 3 ≤ X := by
    rw [R.start_eq]
    omega
  have hmod :
      residueModulus v =
        2 * 2 ^ twoSteps v := by
    unfold residueModulus
    rw [pow_succ]
    ring
  rw [hmod] at hXLower
  nlinarith

/--
tail canonical endpoint が `2 * 3^p` 未満で、
replay quotient が高々2なら、
replay finish は `6 * 3^p` 未満。
-/
theorem ReplayCoordinate.finish_lt_six_mul_threePow_of_quotient_le_two
    {v : Word} {X Y : ℕ}
    (R : ReplayCoordinate v X Y)
    (hCanonicalEnd :
      canonicalEnd v <
        2 * 3 ^ oddSteps v)
    (hqLe : R.quotient ≤ 2) :
    Y < 6 * 3 ^ oddSteps v := by
  have hqScaled :
      2 * 3 ^ oddSteps v * R.quotient ≤
        4 * 3 ^ oddSteps v := by
    calc
      2 * 3 ^ oddSteps v * R.quotient
          ≤ 2 * 3 ^ oddSteps v * 2 :=
        Nat.mul_le_mul_left
          (2 * 3 ^ oddSteps v) hqLe
      _ = 4 * 3 ^ oddSteps v := by
        ring
  calc
    Y
        = canonicalEnd v +
            2 * 3 ^ oddSteps v * R.quotient :=
          R.finish_eq
    _ < 2 * 3 ^ oddSteps v +
          2 * 3 ^ oddSteps v * R.quotient :=
        Nat.add_lt_add_right hCanonicalEnd _
    _ ≤ 2 * 3 ^ oddSteps v +
          4 * 3 ^ oddSteps v :=
        Nat.add_le_add_left hqScaled _
    _ = 6 * 3 ^ oddSteps v := by
        ring

/--
empty word では canonical endpoint と canonical start は一致する。
-/
theorem canonicalEnd_nil_eq_canonicalStart
    (hvalid : Valid ([] : Word)) :
    canonicalEnd ([] : Word) =
      canonicalStart ([] : Word) := by
  have hrun :
      Runs ([] : Word)
        (canonicalStart ([] : Word))
        (canonicalEnd ([] : Word)) :=
    canonicalRuns hvalid
  have hreal := hrun.realizes
  symm
  simpa [Realizes, oddSteps, twoSteps, affineConst] using hreal

/--
empty word の canonical endpoint は endpoint 側 fundamental interval
`[0, 2 * 3^0)` に入る。
-/
theorem canonicalEnd_nil_lt_two_mul_threePow
    (hvalid : Valid ([] : Word)) :
    canonicalEnd ([] : Word) <
      2 * 3 ^ oddSteps ([] : Word) := by
  rw [canonicalEnd_nil_eq_canonicalStart hvalid]
  have hstart :
      canonicalStart ([] : Word) <
        residueModulus ([] : Word) :=
    canonicalStart_lt_modulus ([] : Word)
  simpa [residueModulus, oddSteps, twoSteps] using hstart

/--
valid word の canonical endpoint は endpoint 側 fundamental interval

`[0, 2*3^p)` に入る。
-/
theorem canonicalEnd_lt_two_mul_threePow
    {w : Word}
    (hvalid : Valid w) :
    canonicalEnd w < 2 * 3 ^ oddSteps w := by
  revert hvalid
  induction w with
  | nil =>
      intro hvalid
      exact canonicalEnd_nil_lt_two_mul_threePow hvalid
  | cons e v ih =>
      intro hvalid
      have hrun :
          Runs (e :: v)
            (canonicalStart (e :: v))
            (canonicalEnd (e :: v)) :=
        canonicalRuns hvalid
      cases hrun with
      | @cons _ _ _ y _ he hstep hyOdd htail =>
          have hyLt :
              y < 6 * 2 ^ twoSteps v :=
            canonicalFirstTailStart_lt_six_mul_twoPow hstep
          by_cases hvNil : v = []
          · subst v
            cases htail
            simpa [oddSteps, twoSteps] using hyLt
          · have hvValid : Valid v := by
              intro a ha
              exact hvalid a (by simp [ha])
            have ihTail :
                canonicalEnd v <
                  2 * 3 ^ oddSteps v :=
              ih hvValid
            let R :
                ReplayCoordinate
                  v y (canonicalEnd (e :: v)) :=
              ReplayCoordinate.ofRuns htail hvNil
            have hqLe :
                R.quotient ≤ 2 :=
              R.quotient_le_two_of_start_lt_six_mul_twoPow hyLt
            have hfinishLt :
                canonicalEnd (e :: v) <
                  6 * 3 ^ oddSteps v :=
              R.finish_lt_six_mul_threePow_of_quotient_le_two
                ihTail hqLe
            calc
              canonicalEnd (e :: v)
                  < 6 * 3 ^ oddSteps v := hfinishLt
              _ = 2 * 3 ^ oddSteps (e :: v) := by
                  simp only [oddSteps_cons, pow_succ]
                  ring

end Word
end Collatz2
