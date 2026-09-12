import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.LazyOstrowski

/-!
# Collatz3 Experimental2: lazy Ostrowski code の完全復号

`LazyOstrowski` では canonical lazy representation の存在と一意性を閉じた。
本ファイルでは、その digit 関数だけを独立した code として扱い、

* support より上での zero,
* 任意の十分長い prefix からの exact reconstruction,
* 自然数上での injectivity,
* digit code から元の自然数を戻す decoder,
* list code の encode/decode

をまとめる。

これにより後段の Sturmian path `edgeCount` を、元の path weight を失わない
完全符号として扱える。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/-- canonical lazy representation が持つ digit 関数だけを取り出した公開 code。 -/
noncomputable def canonicalLazyOstrowskiDigits
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) : ℕ → ℕ :=
  (canonicalLazyOstrowskiRepresentation W N).digits

/-- canonical lazy digits は canonical lazy length 以上で `0`。 -/
theorem canonicalLazyOstrowskiDigits_eq_zero_of_large
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    {n : ℕ}
    (hn : ostrowskiLazyLength W N ≤ n) :
    canonicalLazyOstrowskiDigits W N n = 0 := by
  exact (canonicalLazyOstrowskiRepresentation W N).zero_above n hn

/-- canonical lazy digits は support 内で digit bound を満たす。 -/
theorem canonicalLazyOstrowskiDigits_bounded
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    {n : ℕ}
    (hn : n < ostrowskiLazyLength W N) :
    canonicalLazyOstrowskiDigits W N n ≤ W.a n := by
  exact (canonicalLazyOstrowskiRepresentation W N).bounded n hn

/-- canonical lazy digits は support 内で lazy adjacency を満たす。 -/
theorem canonicalLazyOstrowskiDigits_lazy
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    {n : ℕ}
    (hn : n + 1 < ostrowskiLazyLength W N)
    (hZero : canonicalLazyOstrowskiDigits W N (n + 1) = 0) :
    canonicalLazyOstrowskiDigits W N n = W.a n := by
  exact (canonicalLazyOstrowskiRepresentation W N).lazy n hn hZero

/-- canonical support 上では weighted sum が元の `N` に exact に戻る。 -/
theorem canonicalLazyOstrowskiDigits_reconstruct
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    ostrowskiPrefixSum W.Q (canonicalLazyOstrowskiDigits W N)
        (ostrowskiLazyLength W N) = N := by
  exact (canonicalLazyOstrowskiRepresentation W N).value

/--
canonical support より長い prefix を取っても、上位 digit は `0` なので weighted sum は `N` のまま。
-/
theorem canonicalLazyOstrowskiDigits_reconstruct_of_large
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    {t : ℕ}
    (hNt : ostrowskiLazyLength W N ≤ t) :
    ostrowskiPrefixSum W.Q
        (canonicalLazyOstrowskiDigits W N) t = N := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hNt
  clear hNt
  induction s with
  | zero =>
      simpa using canonicalLazyOstrowskiDigits_reconstruct W N
  | succ s ih =>
      rw [show
        ostrowskiLazyLength W N + (s + 1) =
          (ostrowskiLazyLength W N + s) + 1 by
        omega]
      rw [ostrowskiPrefixSum_succ, ih]
      rw [
        canonicalLazyOstrowskiDigits_eq_zero_of_large
          W N (by omega)
      ]
      simp

/-- lazy digit 関数は元の自然数を一意に決める。 -/
theorem canonicalLazyOstrowskiDigits_injective
    (W : UnitOstrowskiWeightSystem) :
    Function.Injective (canonicalLazyOstrowskiDigits W) := by
  intro M N hDigits
  let t := max (ostrowskiLazyLength W M) (ostrowskiLazyLength W N)
  have hM :
      ostrowskiPrefixSum W.Q (canonicalLazyOstrowskiDigits W M) t = M :=
    canonicalLazyOstrowskiDigits_reconstruct_of_large W M
      (by dsimp [t]; omega)
  have hN :
      ostrowskiPrefixSum W.Q (canonicalLazyOstrowskiDigits W N) t = N :=
    canonicalLazyOstrowskiDigits_reconstruct_of_large W N
      (by dsimp [t]; omega)
  calc
    M = ostrowskiPrefixSum W.Q (canonicalLazyOstrowskiDigits W M) t := hM.symm
    _ = ostrowskiPrefixSum W.Q (canonicalLazyOstrowskiDigits W N) t := by rw [hDigits]
    _ = N := hN

/--
lazy digit code が canonical code なら、その元の自然数を返す decoder。
canonical code でない入力には `0` を返す。
-/
noncomputable def canonicalLazyOstrowskiValue
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ) : ℕ := by
  classical
  exact
    if h : ∃ N : ℕ, canonicalLazyOstrowskiDigits W N = d then
      Classical.choose h
    else
      0

/-- canonical lazy digit code を decode すると元の自然数に戻る。 -/
@[simp] theorem canonicalLazyOstrowskiValue_digits
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    canonicalLazyOstrowskiValue W (canonicalLazyOstrowskiDigits W N) = N := by
  have hExists :
      ∃ M : ℕ,
        canonicalLazyOstrowskiDigits W M = canonicalLazyOstrowskiDigits W N :=
    ⟨N, rfl⟩
  rw [canonicalLazyOstrowskiValue, dite_eq_left hExists]
  apply canonicalLazyOstrowskiDigits_injective W
  exact Classical.choose_spec hExists

/-- 自然数列を各要素の canonical lazy digit code の列へ変換する。 -/
noncomputable def lazyOstrowskiLengthCode
    (W : UnitOstrowskiWeightSystem)
    (rs : List ℕ) : List (ℕ → ℕ) :=
  rs.map (canonicalLazyOstrowskiDigits W)

/-- lazy digit-code 列を自然数列へ戻す。 -/
noncomputable def lazyOstrowskiLengthDecode
    (W : UnitOstrowskiWeightSystem)
    (code : List (ℕ → ℕ)) : List ℕ :=
  code.map (canonicalLazyOstrowskiValue W)

/-- lazy list code は encode の直後に decode すると元の列へ exact に戻る。 -/
@[simp] theorem lazyOstrowskiLengthDecode_encode
    (W : UnitOstrowskiWeightSystem)
    (rs : List ℕ) :
    lazyOstrowskiLengthDecode W (lazyOstrowskiLengthCode W rs) = rs := by
  induction rs with
  | nil =>
      simp [lazyOstrowskiLengthCode, lazyOstrowskiLengthDecode]
  | cons r rs ih =>
      change
        canonicalLazyOstrowskiValue W (canonicalLazyOstrowskiDigits W r) ::
            lazyOstrowskiLengthDecode W (lazyOstrowskiLengthCode W rs) =
          r :: rs
      simp [ih]

/-- lazy list code の encode は injective。 -/
theorem lazyOstrowskiLengthCode_injective
    (W : UnitOstrowskiWeightSystem) :
    Function.Injective (lazyOstrowskiLengthCode W) := by
  intro rs ss hCode
  have hDecoded := congrArg (lazyOstrowskiLengthDecode W) hCode
  simpa using hDecoded

end GenericRecordFerrers
end Experimental2
end Collatz3
