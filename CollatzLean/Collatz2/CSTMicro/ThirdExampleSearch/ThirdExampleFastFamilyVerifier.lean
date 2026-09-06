import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteFamilyVerifier

/-!
高速 family verifier。

`ThirdExampleFiniteFamilyVerifier` 側の `familyCheck` が

* 共通2進剥離
* proposed step の一回計算
* count = 1 で singletonCheck へ直接移行
* 空 family の不要な再帰の除去

を持つようになったため、Fast版で別の探索器を二重に維持しない。

Fast API は残し、その実体を高速化済みの通常 verifier に統一する。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh


/-!
既存APIとの互換性のため残す補題。
-/

theorem FamilyDrops.mono
    {s : AffineOrbitState} {a b : Nat}
    (h : FamilyDrops s a)
    (hab : a ≤ b) :
    FamilyDrops s b := by
  intro i hi
  obtain ⟨w, y, hw, hy, hb⟩ := h i hi
  exact
    ⟨w, y, hw, hy,
      Nat.le_trans hb hab⟩


theorem FamilyDrops.step
    {s t : AffineOrbitState} {e b : Nat}
    (h : stepOK s t e)
    (ht : FamilyDrops t b) :
    FamilyDrops s (b + 1) := by

  rcases h with
    ⟨he, hn, hd, hcount, hx, hdx, ho, hdo⟩

  intro i hi

  obtain ⟨w, y, hw, hy, hb⟩ :=
    ht i (by omega)

  refine
    ⟨e :: w,
     y,
     .cons he ?_ ?_ hw,
     ?_,
     ?_⟩

  · calc
      2^e * (t.x0 + t.dx * i)
          =
        2^e * t.x0 +
          (2^e * t.dx) * i := by
            simp only
              [Nat.mul_add,
               Nat.mul_assoc]

      _ =
        3 * s.x0 + 1 +
          (3 * s.dx) * i := by
            rw [hx, hdx]

      _ =
        3 * (s.x0 + s.dx * i) + 1 := by
            simp only
              [Nat.mul_add,
               Nat.mul_assoc]
            omega

  · simp
      [Nat.add_mod,
       Nat.mul_mod,
       ho,
       hdo]

  · simpa [hn, hd] using hy

  · simpa using
      Nat.add_le_add_right hb 1


theorem FamilyDrops.split
    {s : AffineOrbitState} {b : Nat}
    (hl : FamilyDrops (evenFamily s) b)
    (hr : FamilyDrops (oddFamily s) b) :
    FamilyDrops s (b + 1) := by

  intro i hi

  rcases index_partition i s.count hi with h | h

  · obtain ⟨w, y, hw, hy, hb⟩ :=
      hl (i / 2) h.2.1

    have hx :
        s.x0 + s.dx * i =
          (evenFamily s).x0 +
            (evenFamily s).dx * (i / 2) := by
      calc
        _ =
          s.x0 +
            s.dx * (2 * (i / 2)) := by
              exact
                congrArg
                  (fun z => s.x0 + s.dx * z)
                  h.2.2

        _ = _ := by
          simp
            [evenFamily,
             Nat.mul_comm,
             Nat.mul_left_comm]

    have hn :
        s.n0 + s.dn * i =
          (evenFamily s).n0 +
            (evenFamily s).dn * (i / 2) := by
      calc
        _ =
          s.n0 +
            s.dn * (2 * (i / 2)) := by
              exact
                congrArg
                  (fun z => s.n0 + s.dn * z)
                  h.2.2

        _ = _ := by
          simp
            [evenFamily,
             Nat.mul_comm,
             Nat.mul_left_comm]

    exact
      ⟨w,
       y,
       hx ▸ hw,
       hn ▸ hy,
       by omega⟩

  · obtain ⟨w, y, hw, hy, hb⟩ :=
      hr (i / 2) h.2.1

    have hx :
        s.x0 + s.dx * i =
          (oddFamily s).x0 +
            (oddFamily s).dx * (i / 2) := by
      calc
        _ =
          s.x0 +
            s.dx * (2 * (i / 2) + 1) := by
              exact
                congrArg
                  (fun z => s.x0 + s.dx * z)
                  h.2.2

        _ = _ := by
          simp
            [oddFamily,
             Nat.mul_add,
             Nat.mul_comm,
             Nat.mul_left_comm,
             Nat.add_assoc,
             Nat.add_comm]

    have hn :
        s.n0 + s.dn * i =
          (oddFamily s).n0 +
            (oddFamily s).dn * (i / 2) := by
      calc
        _ =
          s.n0 +
            s.dn * (2 * (i / 2) + 1) := by
              exact
                congrArg
                  (fun z => s.n0 + s.dn * z)
                  h.2.2

        _ = _ := by
          simp
            [oddFamily,
             Nat.mul_add,
             Nat.mul_comm,
             Nat.mul_left_comm,
             Nat.add_assoc,
             Nat.add_comm]

    exact
      ⟨w,
       y,
       hx ▸ hw,
       hn ▸ hy,
       by omega⟩


/-!
旧 Fast API との互換性。

新しい familyCheck 自身が count = 1 を直接 scalar checker に落とすため、
実行時には singletonFamily を使用しない。
-/
def singletonFamily
    (s : AffineOrbitState) :
    AffineOrbitState :=
  { s with
      dn := 0
      dx := 0 }


theorem FamilyDrops.singleton
    {s : AffineOrbitState} {b : Nat}
    (hc : s.count = 1)
    (h : FamilyDrops (singletonFamily s) b) :
    FamilyDrops s b := by

  intro i hi

  have hi0 : i = 0 := by
    omega

  subst i

  obtain ⟨w, y, hw, hy, hb⟩ :=
    h 0 (by simp [singletonFamily, hc])

  exact
    ⟨w,
     y,
     by simpa [singletonFamily] using hw,
     by simpa [singletonFamily] using hy,
     hb⟩


/-
====================================================================
  Fast API
====================================================================
-/

/--
高速化済み `proposedExponent` をそのまま利用する。

現在の `proposedExponent` は内部で `proposedStep` を使うため、
旧版のような2本の twoDepth + min ではない。
-/
def fastExponent
    (s : AffineOrbitState) : Nat :=
  proposedExponent s


/--
高速化済み `proposedNext` をそのまま利用する。
-/
def fastNext
    (s : AffineOrbitState) :
    AffineOrbitState :=
  proposedNext s


/--
Fast verifier の実体。

通常 verifier 側がすでにより強い高速化を持つため、
別の探索器は作らず同じ実装を共有する。
-/
def fastFamilyCheck :
    Nat → AffineOrbitState → Bool :=
  familyCheck


@[simp]
theorem fastFamilyCheck_eq
    (fuel : Nat)
    (s : AffineOrbitState) :
    fastFamilyCheck fuel s =
      familyCheck fuel s := by
  rfl


/--
Fast verifier の健全性は、
高速化済み通常 verifier の健全性から直接得られる。
-/
theorem fastFamilyCheck_sound
    {fuel : Nat}
    {s : AffineOrbitState}
    (h : fastFamilyCheck fuel s = true) :
    FamilyDrops s fuel := by

  apply familyCheck_sound

  simpa [fastFamilyCheck] using h


end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
