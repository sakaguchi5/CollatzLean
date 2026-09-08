import CollatzLean.Collatz3.Critical.Profile
import CollatzLean.Collatz3.Core.Word

/-!
# Collatz3: critical word と finite profile の exact equivalence

このファイルでは、Collatz2 に散らばっていた

* prefix two-depth,
* critical roof 以下の有限 word,
* word から profile への抽出,
* profile から exponent word への逆構成

を一つの薄い層にまとめる。

重要なのは、actual orbit の absolute start 値を同値に含めないことである。
ここで同値にするのは有限 first-passage **shape** であり、

  valid exponent word  <->  finite admissible critical profile

を `Equiv` として閉じる。
-/

namespace Collatz3

namespace Word

/-- valid word では隣接 prefix depth が strict に増加する。 -/
theorem prefixTwoDepth_lt_succ_of_valid
    {w : Word}
    (hValid : Valid w)
    {k : ℕ}
    (hk : k < oddSteps w) :
    prefixTwoDepth w k < prefixTwoDepth w (k + 1) := by
  induction w generalizing k with
  | nil =>
      simp [oddSteps] at hk
  | cons e w ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Valid w := by
        intro a ha
        exact hValid a (by simp [ha])
      cases k with
      | zero =>
          simp [prefixTwoDepth, twoSteps, he]
      | succ k =>
          have hkTail : k < oddSteps w := by
            simp only [oddSteps_cons] at hk
            omega
          have hIH := ih hTail hkTail
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            Nat.add_lt_add_left hIH e

/--
prefix depth 全体と長さが一致すれば exponent word 自身も一致する。
各 exponent は隣接 prefix depth の差なので、valid 性すら不要である。
-/
theorem eq_of_oddSteps_eq_of_prefixTwoDepth_eq
    {u v : Word}
    (hLength : oddSteps u = oddSteps v)
    (hDepth :
      ∀ k : ℕ, k ≤ oddSteps u →
        prefixTwoDepth u k = prefixTwoDepth v k) :
    u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons f v =>
          simp [oddSteps] at hLength
  | cons e u ih =>
      cases v with
      | nil =>
          simp [oddSteps] at hLength
      | cons f v =>
          have hTailLength : oddSteps u = oddSteps v := by
            simp only [oddSteps_cons] at hLength
            omega
          have hHeadRaw := hDepth 1 (by simp [oddSteps])
          have hHead : e = f := by
            simpa [prefixTwoDepth, twoSteps] using hHeadRaw
          subst f
          have hTailDepth :
              ∀ k : ℕ, k ≤ oddSteps u →
                prefixTwoDepth u k = prefixTwoDepth v k := by
            intro k hk
            have h := hDepth (k + 1) (by
              simp only [oddSteps_cons]
              omega)
            simp only [prefixTwoDepth_cons_succ] at h
            exact Nat.add_left_cancel h
          have huv := ih hTailLength hTailDepth
          subst v
          rfl

end Word

namespace Critical

/--
幅 `m` の critical first-passage shape を表す word 条件。

* exponent はすべて正、
* odd-step 数は exact に `m`、
* terminal 2-depth は minimal critical depth、
* proper cut は Beatty critical roof 以下。

absolute orbit value はここには入れない。
-/
def IsCriticalWord
    (m : ℕ)
    (w : Word) : Prop :=
  Word.Valid w ∧
  Word.oddSteps w = m ∧
  Word.twoSteps w = criticalTwoDepth m ∧
  ∀ k : ℕ, k < m →
    Word.prefixTwoDepth w k ≤ beattyIndex k

/-- 幅 `m` の critical word shape。 -/
abbrev CriticalWord (m : ℕ) :=
  {w : Word // IsCriticalWord m w}

/-- 幅 `m` の admissible finite critical profile。 -/
abbrev AdmissibleProfile (m : ℕ) :=
  {h : Profile m // Admissible h}

namespace IsCriticalWord

/-- critical word は valid。 -/
theorem valid
    {m : ℕ} {w : Word}
    (C : IsCriticalWord m w) :
    Word.Valid w :=
  C.1

/-- odd-step 数は幅に一致。 -/
theorem oddSteps_eq
    {m : ℕ} {w : Word}
    (C : IsCriticalWord m w) :
    Word.oddSteps w = m :=
  C.2.1

/-- total two-depth は critical terminal depth。 -/
theorem twoSteps_eq
    {m : ℕ} {w : Word}
    (C : IsCriticalWord m w) :
    Word.twoSteps w = criticalTwoDepth m :=
  C.2.2.1

/-- proper prefix は critical roof 以下。 -/
theorem prefixTwoDepth_le_beatty
    {m : ℕ} {w : Word}
    (C : IsCriticalWord m w)
    {k : ℕ}
    (hk : k < m) :
    Word.prefixTwoDepth w k ≤ beattyIndex k :=
  C.2.2.2 k hk

end IsCriticalWord

/--
高さ列の隣接差から exponent word を作る。
これは profile 固有ではない純粋な finite-difference constructor。
-/
def wordFromHeight
    (height : ℕ → ℕ)
    (m : ℕ) : Word :=
  (List.range m).map (fun k => height (k + 1) - height k)

@[simp] theorem oddSteps_wordFromHeight
    (height : ℕ → ℕ)
    (m : ℕ) :
    Word.oddSteps (wordFromHeight height m) = m := by
  simp [wordFromHeight, Word.oddSteps]

/-- strict increasing な高さ列の隣接差はすべて正。 -/
theorem valid_wordFromHeight
    (height : ℕ → ℕ)
    (m : ℕ)
    (hStep : ∀ k : ℕ, k < m → height k < height (k + 1)) :
    Word.Valid (wordFromHeight height m) := by
  intro e he
  unfold wordFromHeight at he
  rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
  have hkLt : k < m := by
    simpa using hk
  exact Nat.sub_pos_of_lt (hStep k hkLt)

/-- 開始高さ 0 なら隣接差の総和は terminal height。 -/
theorem twoSteps_wordFromHeight
    (height : ℕ → ℕ)
    (m : ℕ)
    (hZero : height 0 = 0)
    (hStep : ∀ k : ℕ, k < m → height k < height (k + 1)) :
    Word.twoSteps (wordFromHeight height m) = height m := by
  unfold Word.twoSteps wordFromHeight
  revert hStep
  induction m with
  | zero =>
      intro hStep
      simp [hZero]
  | succ m ih =>
      intro hStep
      have hPrev : ∀ k : ℕ, k < m → height k < height (k + 1) := by
        intro k hk
        exact hStep k (by omega)
      have hIH := ih hPrev
      have hLast := hStep m (by omega)
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      rw [hIH]
      omega

/-- `k ≤ m` なら生成 word の prefix depth は指定 height `k` に戻る。 -/
theorem prefixTwoDepth_wordFromHeight
    (height : ℕ → ℕ)
    (m : ℕ)
    (hZero : height 0 = 0)
    (hStep : ∀ i : ℕ, i < m → height i < height (i + 1))
    {k : ℕ}
    (hk : k ≤ m) :
    Word.prefixTwoDepth (wordFromHeight height m) k = height k := by
  unfold Word.prefixTwoDepth wordFromHeight
  rw [← List.map_take]
  rw [List.take_range, Nat.min_eq_left hk]
  exact twoSteps_wordFromHeight height k hZero
    (fun i hi => hStep i (lt_of_lt_of_le hi hk))

/--
profile から読む prefix-height path。
proper cut では checkpoint、terminal cut `m` では critical terminal depth を置く。
-/
def profileHeight
    {m : ℕ}
    (h : Profile m)
    (k : ℕ) : ℕ :=
  if hk : k < m then
    checkpoint h ⟨k, hk⟩
  else
    criticalTwoDepth m

@[simp] theorem profileHeight_of_lt
    {m : ℕ}
    (h : Profile m)
    {k : ℕ}
    (hk : k < m) :
    profileHeight h k = checkpoint h ⟨k, hk⟩ := by
  simp [profileHeight, hk]

@[simp] theorem profileHeight_terminal
    {m : ℕ}
    (h : Profile m) :
    profileHeight h m = criticalTwoDepth m := by
  simp [profileHeight]

/-- positive width の admissible profile は height 0 から始まる。 -/
theorem profileHeight_zero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    profileHeight h 0 = 0 := by
  rw [profileHeight_of_lt h hm]
  exact A.first_checkpoint_eq_zero hm

/-- admissible profile の height path は terminal まで strict に増加する。 -/
theorem profileHeight_lt_succ
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {k : ℕ}
    (hk : k < m) :
    profileHeight h k < profileHeight h (k + 1) := by
  rw [profileHeight_of_lt h hk]
  by_cases hNext : k + 1 < m
  · rw [profileHeight_of_lt h hNext]
    exact A.checkpoint_strict hNext
  · have hEq : k + 1 = m := by omega
    have hRight : profileHeight h (k + 1) = criticalTwoDepth m := by
      rw [hEq]
      exact profileHeight_terminal h
    rw [hRight]
    have hCheckpointLe :
        checkpoint h ⟨k, hk⟩ ≤ beattyIndex k := by
      unfold checkpoint
      exact Nat.sub_le _ _
    have hBeattySucc : beattyIndex k < beattyIndex (k + 1) :=
      beattyIndex_lt_succ k
    have hBeatty : beattyIndex k < beattyIndex m := by
      simpa [hEq] using hBeattySucc
    unfold criticalTwoDepth
    omega

/-- admissible profile の exact exponent word。 -/
def wordOfProfile
    {m : ℕ}
    (h : Profile m) : Word :=
  wordFromHeight (profileHeight h) m

@[simp] theorem oddSteps_wordOfProfile
    {m : ℕ}
    (h : Profile m) :
    Word.oddSteps (wordOfProfile h) = m := by
  exact oddSteps_wordFromHeight (profileHeight h) m

/-- admissible profile から作る word は valid。 -/
theorem valid_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    Word.Valid (wordOfProfile h) := by
  exact valid_wordFromHeight (profileHeight h) m
    (fun k hk => profileHeight_lt_succ A hk)

/-- positive width では profile の terminal depth が exact に word total depth となる。 -/
theorem twoSteps_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    Word.twoSteps (wordOfProfile h) = criticalTwoDepth m := by
  calc
    Word.twoSteps (wordOfProfile h)
        = profileHeight h m :=
          twoSteps_wordFromHeight
            (profileHeight h) m
            (profileHeight_zero A hm)
            (fun k hk => profileHeight_lt_succ A hk)
    _ = criticalTwoDepth m := profileHeight_terminal h

/-- profile から生成した word の prefix depth は profile height に exact に戻る。 -/
theorem prefixTwoDepth_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m)
    {k : ℕ}
    (hk : k ≤ m) :
    Word.prefixTwoDepth (wordOfProfile h) k = profileHeight h k := by
  exact prefixTwoDepth_wordFromHeight
    (profileHeight h) m
    (profileHeight_zero A hm)
    (fun i hi => profileHeight_lt_succ A hi)
    hk

/-- admissible profile は critical word shape を exact に生成する。 -/
theorem isCriticalWord_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    IsCriticalWord m (wordOfProfile h) := by
  refine ⟨valid_wordOfProfile A, oddSteps_wordOfProfile h,
    twoSteps_wordOfProfile A hm, ?_⟩
  intro k hk
  have hPrefix :=
    prefixTwoDepth_wordOfProfile A hm (Nat.le_of_lt hk)
  rw [hPrefix, profileHeight_of_lt h hk]
  unfold checkpoint
  exact Nat.sub_le _ _

/-- word の proper prefix depth を Beatty roof から引いて profile にする。 -/
def profileOfWord
    {m : ℕ}
    (w : Word) : Profile m :=
  fun k => beattyIndex k.1 - Word.prefixTwoDepth w k.1

/-- critical word から作った profile の checkpoint は元 prefix depthそのもの。 -/
theorem checkpoint_profileOfWord
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w)
    (k : Fin m) :
    checkpoint (profileOfWord w) k = Word.prefixTwoDepth w k.1 := by
  unfold checkpoint profileOfWord
  have hLe := C.prefixTwoDepth_le_beatty k.2
  omega

/-- critical word から抽出した finite profile は admissible。 -/
theorem admissible_profileOfWord
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w) :
    Admissible (profileOfWord (m := m) w) := by
  constructor
  · intro k
    unfold profileOfWord
    exact Nat.sub_le _ _
  · intro k hk
    rw [checkpoint_profileOfWord C ⟨k, by omega⟩]
    rw [checkpoint_profileOfWord C ⟨k + 1, hk⟩]
    apply Word.prefixTwoDepth_lt_succ_of_valid C.valid
    rw [C.oddSteps_eq]
    omega

/-- profile -> word -> profile は exact identity。 -/
theorem profileOfWord_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    profileOfWord (wordOfProfile h) = h := by
  funext k
  unfold profileOfWord
  have hPrefix :=
    prefixTwoDepth_wordOfProfile A hm (Nat.le_of_lt k.2)
  rw [hPrefix, profileHeight_of_lt h k.2]
  unfold checkpoint
  have hLe := A.depth_le k
  change beattyIndex k.1 - (beattyIndex k.1 - h k) = h k
  omega

/-- critical word 抽出 profile の height は、terminal を含め元 prefix depthに戻る。 -/
theorem profileHeight_profileOfWord
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w)
    {k : ℕ}
    (hk : k ≤ m) :
    profileHeight (profileOfWord (m := m) w)  k = Word.prefixTwoDepth w k := by
  by_cases hProper : k < m
  · rw [profileHeight_of_lt (profileOfWord w) hProper]
    exact checkpoint_profileOfWord C ⟨k, hProper⟩
  · have hEq : k = m := by omega
    subst k
    rw [profileHeight_terminal]
    symm
    calc
      Word.prefixTwoDepth w m
          = Word.prefixTwoDepth w (Word.oddSteps w) := by
              rw [C.oddSteps_eq]
      _ = Word.twoSteps w := Word.prefixTwoDepth_oddSteps w
      _ = criticalTwoDepth m := C.twoSteps_eq

/-- word -> profile -> word も exact identity。 -/
theorem wordOfProfile_profileOfWord
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w)
    (hm : 0 < m) :
    wordOfProfile (profileOfWord (m := m) w)  = w := by
  let A : Admissible (profileOfWord w) := admissible_profileOfWord C
  apply Word.eq_of_oddSteps_eq_of_prefixTwoDepth_eq
  · calc
      Word.oddSteps (wordOfProfile (profileOfWord w)) = m :=
        oddSteps_wordOfProfile (profileOfWord w)
      _ = Word.oddSteps w := C.oddSteps_eq.symm
  · intro k hk
    have hkM : k ≤ m := by
      rw [oddSteps_wordOfProfile] at hk
      exact hk
    rw [prefixTwoDepth_wordOfProfile A hm hkM]
    exact profileHeight_profileOfWord C hkM

/--
positive width `m` では、critical first-passage word shape と
finite admissible profile は本当に `Equiv`。
-/
def criticalWordEquivAdmissibleProfile
    (m : ℕ)
    (hm : 0 < m) :
    CriticalWord m ≃ AdmissibleProfile m where
  toFun W :=
    ⟨profileOfWord W.1, admissible_profileOfWord W.2⟩
  invFun H :=
    ⟨wordOfProfile H.1, isCriticalWord_wordOfProfile H.2 hm⟩
  left_inv W := by
    apply Subtype.ext
    exact wordOfProfile_profileOfWord W.2 hm
  right_inv H := by
    apply Subtype.ext
    exact profileOfWord_wordOfProfile H.2 hm

end Critical
end Collatz3
