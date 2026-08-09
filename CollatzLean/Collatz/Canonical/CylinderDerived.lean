import CollatzLean.Collatz.Canonical.Cylinder

/-!
# canonical cylinderの合成・shadow・contracting replay

cylinder digitのmixed-radix合成則、canonical shadow magnitudeの更新、
contracting wordのreplay gap減少を有限語層でまとめる。
-/

namespace Collatz
namespace Word

/--
右suffixを二段階で付けたときのcylinder digit合成則。
`v`の総2進指数をradixとしてmixed-radixに合成される。
-/
theorem extensionDigit_append
    {u v w : Collatz.Word}
    (hvalid : ((u ++ v) ++ w).Valid)
    (hu : u ≠ []) :
    u.extensionDigit (v ++ w) =
      u.extensionDigit v +
        2 ^ v.twoSteps * (u ++ v).extensionDigit w := by
  have huvValid : (u ++ v).Valid :=
    hvalid.prefix
  have hallValid : (u ++ (v ++ w)).Valid := by
    simpa [List.append_assoc] using hvalid
  have huvNe : u ++ v ≠ [] := by
    cases u with
    | nil => contradiction
    | cons a u => simp
  have htotal :=
    canonicalStart_append_eq
      (u := u) (v := v ++ w) hallValid hu
  have hfirst :=
    canonicalStart_append_eq
      (u := u) (v := v) huvValid hu
  have hsecond :=
    canonicalStart_append_eq
      (u := u ++ v) (v := w) hvalid huvNe
  have hmodulus :
      (u ++ v).residueModulus =
        u.residueModulus * 2 ^ v.twoSteps := by
    simp [residueModulus, twoSteps_append, pow_add]
    ac_rfl
  have heq :
      u.canonicalStart +
          u.residueModulus * u.extensionDigit (v ++ w) =
        u.canonicalStart +
          u.residueModulus *
            (u.extensionDigit v +
              2 ^ v.twoSteps * (u ++ v).extensionDigit w) := by
    calc
      u.canonicalStart +
          u.residueModulus * u.extensionDigit (v ++ w)
          = (u ++ (v ++ w)).canonicalStart := htotal.symm
      _ = ((u ++ v) ++ w).canonicalStart := by
            simp [List.append_assoc]
      _ = (u ++ v).canonicalStart +
            (u ++ v).residueModulus *
              (u ++ v).extensionDigit w := hsecond
      _ = (u.canonicalStart +
              u.residueModulus * u.extensionDigit v) +
            (u.residueModulus * 2 ^ v.twoSteps) *
              (u ++ v).extensionDigit w := by
            rw [hfirst, hmodulus]
      _ = u.canonicalStart +
            u.residueModulus *
              (u.extensionDigit v +
                2 ^ v.twoSteps * (u ++ v).extensionDigit w) := by
            ring
  have hmul :
      u.residueModulus * u.extensionDigit (v ++ w) =
        u.residueModulus *
          (u.extensionDigit v +
            2 ^ v.twoSteps * (u ++ v).extensionDigit w) :=
    Nat.add_left_cancel heq
  have hmodulusPos : 0 < u.residueModulus := by
    simp [residueModulus]
  exact Nat.mul_left_cancel hmodulusPos hmul

/-- canonical modulus上端からstartまでの自然数距離。 -/
def canonicalShadowMagnitude (w : Collatz.Word) : ℕ :=
  w.residueModulus - w.canonicalStart

/--
一文字延長におけるcanonical shadow magnitudeのexact更新式。
maximal digitでのみ増分が0になる。
-/
theorem canonicalShadowMagnitude_append_singleton
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    (u ++ [e]).canonicalShadowMagnitude =
      u.canonicalShadowMagnitude +
        u.residueModulus *
          (2 ^ e - 1 - u.extensionDigit [e]) := by
  have hstart :=
    canonicalStart_append_eq
      (u := u) (v := [e]) hvalid hu
  have hmodulus :
      (u ++ [e]).residueModulus =
        u.residueModulus * 2 ^ e := by
    simp [residueModulus, pow_add, Nat.add_comm,
      Nat.add_left_comm, Nat.mul_comm]
  have hbound :=
    extensionDigit_singleton_lt_twoPow
      (u := u) (e := e) hvalid hu
  let r := 2 ^ e - 1 - u.extensionDigit [e]
  have hdigitLe :
      u.extensionDigit [e] ≤ 2 ^ e - 1 := by
    omega
  have hr :
      u.extensionDigit [e] + 1 + r = 2 ^ e := by
    dsimp [r]
    omega
  have hbaseLe :
      u.canonicalStart ≤ u.residueModulus :=
    (canonicalStart_lt_modulus u).le
  have hbase :
      u.canonicalStart + u.canonicalShadowMagnitude =
        u.residueModulus := by
    unfold canonicalShadowMagnitude
    omega
  have hsum :
      (u ++ [e]).canonicalStart +
          (u.canonicalShadowMagnitude +
            u.residueModulus * r) =
        (u ++ [e]).residueModulus := by
    rw [hstart, hmodulus]
    calc
      u.canonicalStart +
            u.residueModulus * u.extensionDigit [e] +
          (u.canonicalShadowMagnitude +
            u.residueModulus * r)
          =
        (u.canonicalStart + u.canonicalShadowMagnitude) +
          u.residueModulus * u.extensionDigit [e] +
          u.residueModulus * r := by
            ring
      _ = u.residueModulus +
          u.residueModulus * u.extensionDigit [e] +
          u.residueModulus * r := by
            rw [hbase]
      _ = u.residueModulus *
          (u.extensionDigit [e] + 1 + r) := by
            ring
      _ = u.residueModulus * 2 ^ e := by
            rw [hr]
  have hnextLe :
      (u ++ [e]).canonicalStart ≤
        (u ++ [e]).residueModulus :=
    (canonicalStart_lt_modulus (u ++ [e])).le
  have hresult :
      (u ++ [e]).residueModulus -
          (u ++ [e]).canonicalStart =
        u.canonicalShadowMagnitude +
          u.residueModulus * r := by
    omega
  simpa [canonicalShadowMagnitude, r] using hresult

/-- 一文字延長でcanonical shadow magnitudeは単調非減少。 -/
theorem canonicalShadowMagnitude_le_append_singleton
    {u : Collatz.Word} {e : ℕ}
    (hvalid : (u ++ [e]).Valid)
    (hu : u ≠ []) :
    u.canonicalShadowMagnitude ≤
      (u ++ [e]).canonicalShadowMagnitude := by
  rw [canonicalShadowMagnitude_append_singleton hvalid hu]
  omega

/-- contracting語のmultiplicative gap `2^H-3^p`。 -/
def contractingGap (w : Collatz.Word) : ℕ :=
  2 ^ w.twoSteps - 3 ^ w.oddSteps

/-- contractingならmultiplicative gapは正。 -/
theorem Contracting.contractingGap_pos
    {w : Collatz.Word} (hC : w.Contracting) :
    0 < w.contractingGap := by
  unfold contractingGap Contracting at *
  omega

/--
contracting wordのcanonical replayでは、一段上がるごとに
start-end差へ`2 * contractingGap`がexactに加わる。
減算を使わないbalance形。
-/
theorem Contracting.replayGap_balance
    {w : Collatz.Word}
    (hC : w.Contracting)
    (j : ℕ) :
    (w.canonicalEnd + 2 * 3 ^ w.oddSteps * j) +
        2 * w.contractingGap * j +
        w.canonicalStart =
      (w.canonicalStart + w.residueModulus * j) +
        w.canonicalEnd := by
  have hgap :
      3 ^ w.oddSteps + w.contractingGap =
        2 ^ w.twoSteps := by
    unfold Contracting at hC
    unfold contractingGap
    omega
  have hmodulus :
      w.residueModulus = 2 * 2 ^ w.twoSteps := by
    unfold residueModulus
    rw [pow_succ]
    ring
  rw [hmodulus]
  calc
    (w.canonicalEnd + 2 * 3 ^ w.oddSteps * j) +
          2 * w.contractingGap * j +
          w.canonicalStart
        =
      w.canonicalStart + w.canonicalEnd +
        2 * (3 ^ w.oddSteps + w.contractingGap) * j := by
          ring
    _ = w.canonicalStart + w.canonicalEnd +
        2 * 2 ^ w.twoSteps * j := by
          rw [hgap]
    _ =
      (w.canonicalStart + (2 * 2 ^ w.twoSteps) * j) +
        w.canonicalEnd := by
          ring

/--
contracting wordのreplay level `j`がまだpositive returnなら、
そのreturn gapはcanonical gapから`2*g*j`だけ減ったもの。
-/
theorem Contracting.replayGap
    {w : Collatz.Word}
    (hC : w.Contracting)
    (j : ℕ)
    (hpos :
      w.canonicalStart + w.residueModulus * j ≤
        w.canonicalEnd + 2 * 3 ^ w.oddSteps * j) :
    (w.canonicalEnd + 2 * 3 ^ w.oddSteps * j -
        (w.canonicalStart + w.residueModulus * j)) +
      2 * w.contractingGap * j =
        w.canonicalEnd - w.canonicalStart := by
  have hbalance := hC.replayGap_balance j
  have hcanonical :
      w.canonicalStart ≤ w.canonicalEnd := by
    omega
  omega

/--
suffixを一文字ずつ伸ばす全段階でcylinder digitが0であること。
-/
def AllExtensionDigitsZero (u : Collatz.Word) : Collatz.Word → Prop
  | [] => True
  | e :: v =>
      u.extensionDigit [e] = 0 ∧
        AllExtensionDigitsZero (u ++ [e]) v

/--
aggregate cylinder digitが0なら、そのsuffix内部の全一文字digitも0。
mixed-radix合成則の非負性から従う。
-/
theorem allExtensionDigitsZero_of_extensionDigit_eq_zero
    {u v : Collatz.Word}
    (hvalid : (u ++ v).Valid)
    (hu : u ≠ [])
    (hzero : u.extensionDigit v = 0) :
    u.AllExtensionDigitsZero v := by
  induction v generalizing u with
  | nil =>
      simp [AllExtensionDigitsZero]
  | cons e v ih =>
      have hvalidAssoc :
          ((u ++ [e]) ++ v).Valid := by
        simpa [List.append_assoc] using hvalid
      have hvalidHead : (u ++ [e]).Valid :=
        hvalidAssoc.prefix
      have huHead : u ++ [e] ≠ [] := by
        cases u with
        | nil => contradiction
        | cons a u => simp
      have hcomp :=
        extensionDigit_append
          (u := u) (v := [e]) (w := v)
          hvalidAssoc hu
      have hsum :
          u.extensionDigit [e] +
              2 ^ e * (u ++ [e]).extensionDigit v = 0 := by
        have hzero' :
            u.extensionDigit ([e] ++ v) = 0 := by
          simpa using hzero
        rw [hcomp] at hzero'
        simpa [twoSteps] using hzero'
      have hheadZero :
          u.extensionDigit [e] = 0 := by
        omega
      have hmulZero :
          2 ^ e * (u ++ [e]).extensionDigit v = 0 := by
        omega
      have htailZero :
          (u ++ [e]).extensionDigit v = 0 := by
        rcases Nat.mul_eq_zero.mp hmulZero with hpow | htail
        · have hpowPos : 0 < 2 ^ e :=
            Nat.pow_pos (by omega)
          omega
        · exact htail
      change
        u.extensionDigit [e] = 0 ∧
          (u ++ [e]).AllExtensionDigitsZero v
      exact
        ⟨hheadZero,
          ih hvalidAssoc huHead htailZero⟩

end Word
end Collatz
