import CollatzLean.Collatz3.Binary.Runs


/-!
# Collatz3 Binary: finite run resolution

run length `a` を threshold `t` まで exact に保持し、それより長い場合は parity だけを保持する。

探索段階の `S / E / O` quotient を一般の `t` に拡張したものだが、
専用 inductive type は作らず自然数 code 一つだけで表す。

重要なのは、`t+2` の情報が

* run length を 1 減らした後の `t` 情報
* run length を 2 減らした後の `t` 情報

を決める、という局所 factor theorem である。
-/

namespace Collatz3
namespace Binary

/--
run length の resolution code。

* `a ≤ t` なら `2*a` として exact に保持する。
* `t < a` なら `2*(t+1) + a%2` として long-run parity だけ保持する。
-/
def runResolutionCode (t a : ℕ) : ℕ :=
  if a ≤ t then
    2 * a
  else
    2 * (t + 1) + a % 2

/-- run-length list 全体の resolution。 -/
def resolveRunLengths (t : ℕ) (lengths : List ℕ) : List ℕ :=
  lengths.map (runResolutionCode t)

/-- binary word の run resolution。 -/
def runResolution (t : ℕ) (bits : List Bool) : List ℕ :=
  resolveRunLengths t (runLengths bits)

/-- short run は exact code。 -/
theorem runResolutionCode_of_le
    {t a : ℕ}
    (h : a ≤ t) :
    runResolutionCode t a = 2 * a := by
  simp [runResolutionCode, h]

/-- long run は parity code。 -/
theorem runResolutionCode_of_lt
    {t a : ℕ}
    (h : t < a) :
    runResolutionCode t a = 2 * (t + 1) + a % 2 := by
  simp [runResolutionCode, Nat.not_le.mpr h]

/--
`t+2` resolution が同じ二つの run は、`t` resolution でも同じ。
-/
theorem runResolutionCode_factor_two
    {t a b : ℕ}
    (h : runResolutionCode (t + 2) a = runResolutionCode (t + 2) b) :
    runResolutionCode t a = runResolutionCode t b := by
  by_cases ha : a ≤ t + 2
  · by_cases hb : b ≤ t + 2
    · have hab : a = b := by
        rw [runResolutionCode_of_le ha, runResolutionCode_of_le hb] at h
        omega
      subst b
      rfl
    · have hb' : t + 2 < b := Nat.lt_of_not_ge hb
      have hbmod : b % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [runResolutionCode_of_le ha, runResolutionCode_of_lt hb'] at h
      omega
  · have ha' : t + 2 < a := Nat.lt_of_not_ge ha
    by_cases hb : b ≤ t + 2
    · have hamod : a % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [runResolutionCode_of_lt ha', runResolutionCode_of_le hb] at h
      omega
    · have hb' : t + 2 < b := Nat.lt_of_not_ge hb
      have htA : t < a := by omega
      have htB : t < b := by omega
      rw [runResolutionCode_of_lt ha', runResolutionCode_of_lt hb'] at h
      rw [runResolutionCode_of_lt htA, runResolutionCode_of_lt htB]
      omega

/--
`t+2` resolution が同じなら、双方の run length を 1 減らした後の `t` resolution も同じ。
-/
theorem runResolutionCode_sub_one_factor
    {t a b : ℕ}
    (h : runResolutionCode (t + 2) a = runResolutionCode (t + 2) b) :
    runResolutionCode t (a - 1) = runResolutionCode t (b - 1) := by
  by_cases ha : a ≤ t + 2
  · by_cases hb : b ≤ t + 2
    · have hab : a = b := by
        rw [runResolutionCode_of_le ha, runResolutionCode_of_le hb] at h
        omega
      subst b
      rfl
    · have hb' : t + 2 < b := Nat.lt_of_not_ge hb
      have hbmod : b % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [runResolutionCode_of_le ha, runResolutionCode_of_lt hb'] at h
      omega
  · have ha' : t + 2 < a := Nat.lt_of_not_ge ha
    by_cases hb : b ≤ t + 2
    · have hamod : a % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [runResolutionCode_of_lt ha', runResolutionCode_of_le hb] at h
      omega
    · have hb' : t + 2 < b := Nat.lt_of_not_ge hb
      have hA : t < a - 1 := by omega
      have hB : t < b - 1 := by omega
      rw [runResolutionCode_of_lt ha', runResolutionCode_of_lt hb'] at h
      rw [runResolutionCode_of_lt hA, runResolutionCode_of_lt hB]
      omega

/--
`t+2` resolution が同じなら、双方の run length を 2 減らした後の `t` resolution も同じ。
これが `3x+1` の run-local tableで必要になる中心情報量補題。
-/
theorem runResolutionCode_sub_two_factor
    {t a b : ℕ}
    (h : runResolutionCode (t + 2) a = runResolutionCode (t + 2) b) :
    runResolutionCode t (a - 2) = runResolutionCode t (b - 2) := by
  by_cases ha : a ≤ t + 2
  · by_cases hb : b ≤ t + 2
    · have hab : a = b := by
        rw [runResolutionCode_of_le ha, runResolutionCode_of_le hb] at h
        omega
      subst b
      rfl
    · have hb' : t + 2 < b := Nat.lt_of_not_ge hb
      have hbmod : b % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [runResolutionCode_of_le ha, runResolutionCode_of_lt hb'] at h
      omega
  · have ha' : t + 2 < a := Nat.lt_of_not_ge ha
    by_cases hb : b ≤ t + 2
    · have hamod : a % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [runResolutionCode_of_lt ha', runResolutionCode_of_le hb] at h
      omega
    · have hb' : t + 2 < b := Nat.lt_of_not_ge hb
      have hA : t < a - 2 := by omega
      have hB : t < b - 2 := by omega
      rw [runResolutionCode_of_lt ha', runResolutionCode_of_lt hb'] at h
      rw [runResolutionCode_of_lt hA, runResolutionCode_of_lt hB]
      omega

/-- list 全体でも `t+2` equality は `t` equality へ降りる。 -/
theorem resolveRunLengths_factor_two
    {t : ℕ} {a b : List ℕ}
    (h : resolveRunLengths (t + 2) a = resolveRunLengths (t + 2) b) :
    resolveRunLengths t a = resolveRunLengths t b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons x xs =>
          simp [resolveRunLengths] at h
  | cons x xs ih =>
      cases b with
      | nil =>
          simp [resolveRunLengths] at h
      | cons y ys =>
          have hHead :
              runResolutionCode (t + 2) x =
                runResolutionCode (t + 2) y := by
            simpa [resolveRunLengths] using congrArg List.head? h
          have hTail :
              resolveRunLengths (t + 2) xs =
                resolveRunLengths (t + 2) ys := by
            simpa [resolveRunLengths] using congrArg List.tail h
          have hHeadLow :
              runResolutionCode t x =
                runResolutionCode t y :=
            runResolutionCode_factor_two hHead
          have hTailLow :
              resolveRunLengths t xs =
                resolveRunLengths t ys :=
            ih hTail
          have hTailMap :
              List.map (runResolutionCode t) xs =
                List.map (runResolutionCode t) ys := by
            simpa [resolveRunLengths] using ih hTail
          simp only [resolveRunLengths, List.map_cons]
          exact congrArg₂ List.cons hHeadLow hTailMap

/-- binary word に対する coarse factor。 -/
theorem runResolution_factor_two
    {t : ℕ} {u v : List Bool}
    (h : runResolution (t + 2) u = runResolution (t + 2) v) :
    runResolution t u = runResolution t v := by
  unfold runResolution at h ⊢
  exact resolveRunLengths_factor_two h

end Binary
end Collatz3
