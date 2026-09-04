import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleComputableBoundaryDigit

/-!
# 第3例探索 D3.2: 分岐しない 42 段 Hensel fold

D3.1 では、一つの boundary constraint が許す digit を `Fin 3` の有限計算へ落とした。
ここでは「各段で使う digit が一意に供給された」後の Hensel 計算を、
分岐木ではなく一本の決定的 fold として実装する。

このファイルは、同じ criticalization boundary digit を42回使うとは仮定しない。
各段の digit provider は独立に与えられ、後段の compatibility theorem が
actual endpoint の各 ternary digit と一致することを証明する。

従ってここで確定するのは

  3-way branch x 42

ではなく

  42 回の deterministic step

という実行形である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
`r` 桁まで決まった residue `q` に、指定された一桁 `digit` を付ける決定的 step。
-/
def thirdExampleForcedHenselStep
    (q r : ℕ)
    (digit : Fin 3) : ℕ :=
  q + digit.val * 3 ^ r

/-- 新しい digit を付けても下位 `r` 桁は変わらない。 -/
theorem thirdExampleForcedHenselStep_mod_basePow
    (q r : ℕ)
    (digit : Fin 3) :
    thirdExampleForcedHenselStep q r digit % (3 ^ r) =
      q % (3 ^ r) := by
  simp [thirdExampleForcedHenselStep, Nat.add_mod]

/--
`digit 0, digit 1, ...` を下位から順に積む決定的 prefix fold。
provider は純粋な計算関数であり、proof object は含まない。
-/
def thirdExampleForcedHenselPrefix
    (digit : ℕ → Fin 3) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      thirdExampleForcedHenselStep
        (thirdExampleForcedHenselPrefix digit r)
        r
        (digit r)

@[simp] theorem thirdExampleForcedHenselPrefix_zero
    (digit : ℕ → Fin 3) :
    thirdExampleForcedHenselPrefix digit 0 = 0 := rfl

@[simp] theorem thirdExampleForcedHenselPrefix_succ
    (digit : ℕ → Fin 3)
    (r : ℕ) :
    thirdExampleForcedHenselPrefix digit (r + 1) =
      thirdExampleForcedHenselStep
        (thirdExampleForcedHenselPrefix digit r)
        r
        (digit r) := rfl

/--
任意の digit provider でも、`R` 桁 fold は必ず canonical range `0 <= q < 3^R` に収まる。
各 digit が `0,1,2` であることだけを使う。
-/
theorem thirdExampleForcedHenselPrefix_lt_pow
    (digit : ℕ → Fin 3)
    (R : ℕ) :
    thirdExampleForcedHenselPrefix digit R < 3 ^ R := by
  induction R with
  | zero =>
      simp [thirdExampleForcedHenselPrefix]
  | succ R ih =>
      rw [thirdExampleForcedHenselPrefix_succ]
      unfold thirdExampleForcedHenselStep
      have hDigitLt : (digit R).val < 3 := (digit R).isLt
      have hDigitLe : (digit R).val ≤ 2 := by
        omega
      have hMul :
          (digit R).val * 3 ^ R ≤ 2 * 3 ^ R :=
        Nat.mul_le_mul_right (3 ^ R) hDigitLe
      have hSum :
          thirdExampleForcedHenselPrefix digit R +
              (digit R).val * 3 ^ R <
            3 ^ R + 2 * 3 ^ R :=
        Nat.add_lt_add_of_lt_of_le ih hMul
      rw [pow_succ]
      omega

/--
provider の最初の `R` digits が actual endpoint `y` の ternary digits と一致するなら、
決定的 fold は既存の actual Hensel prefix fold と exact に一致する。
-/
theorem thirdExampleForcedHenselPrefix_eq_actual
    (digit : ℕ → Fin 3)
    (y : ℕ) :
    ∀ R : ℕ,
      (∀ r : ℕ, r < R →
        digit r = gapOneThreeAdicDigitFin y r) →
      thirdExampleForcedHenselPrefix digit R =
        gapOneHenselPrefixFold y R := by
  intro R
  induction R with
  | zero =>
      intro hDigit
      rfl
  | succ R ih =>
      intro hDigit
      rw [thirdExampleForcedHenselPrefix_succ]
      rw [gapOneHenselPrefixFold_succ]
      unfold thirdExampleForcedHenselStep
      have hPrefix :
          thirdExampleForcedHenselPrefix digit R =
            gapOneHenselPrefixFold y R := by
        apply ih
        intro r hr
        exact hDigit r (Nat.lt_trans hr (Nat.lt_succ_self R))
      rw [hPrefix]
      have hLast :
          digit R = gapOneThreeAdicDigitFin y R :=
        hDigit R (Nat.lt_succ_self R)
      rw [hLast]
      simp

/-- 第3例 right collar に固定した 42 段 deterministic Hensel fold。 -/
def thirdExampleForcedHensel42
    (digit : ℕ → Fin 3) : ℕ :=
  thirdExampleForcedHenselPrefix digit 42

/-- 42段の結果は常に `3^42` 未満の canonical representative。 -/
theorem thirdExampleForcedHensel42_lt_rightModulus
    (digit : ℕ → Fin 3) :
    thirdExampleForcedHensel42 digit <
      thirdExampleRightModulus := by
  simpa [thirdExampleForcedHensel42, thirdExampleRightModulus] using
    thirdExampleForcedHenselPrefix_lt_pow digit 42

/--
最初の42 digits が actual endpoint `y` と一致すれば、一本鎖 fold の最終値は
exact に `y mod 3^42`。

ここにも `y < 3^42` は不要。
-/
theorem thirdExampleForcedHensel42_eq_mod
    (digit : ℕ → Fin 3)
    (y : ℕ)
    (hDigit :
      ∀ r : ℕ, r < 42 →
        digit r = gapOneThreeAdicDigitFin y r) :
    thirdExampleForcedHensel42 digit =
      y % thirdExampleRightModulus := by
  calc
    thirdExampleForcedHensel42 digit =
        gapOneHenselPrefixFold y 42 := by
      exact thirdExampleForcedHenselPrefix_eq_actual digit y 42 hDigit
    _ = thirdExampleHensel42Residue y := rfl
    _ = y % thirdExampleRightModulus :=
      thirdExampleHensel42Residue_eq_mod y

/--
actual endpoint 自身の digit provider。
これは soundness の基準用であり、最終 verifier は boundary から計算した provider を使う。
-/
def thirdExampleActualHenselDigitProvider
    (y : ℕ)
    (r : ℕ) : Fin 3 :=
  gapOneThreeAdicDigitFin y r

/-- actual provider を使えば42段 fold は当然 actual endpoint residue に一致する。 -/
@[simp] theorem thirdExampleForcedHensel42_actualProvider
    (y : ℕ) :
    thirdExampleForcedHensel42
        (thirdExampleActualHenselDigitProvider y) =
      y % thirdExampleRightModulus := by
  apply thirdExampleForcedHensel42_eq_mod
  intro r hr
  rfl

end ThirdExampleSearch
end CSTMicro
end Collatz2
