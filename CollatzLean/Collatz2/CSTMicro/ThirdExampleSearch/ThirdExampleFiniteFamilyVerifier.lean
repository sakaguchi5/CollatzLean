import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleAffineCertificate
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleBranchArithmetic

/-!
第三例の高枝用 affine-family 検査器。

高速化の要点:

1. `proposedExponent` と `proposedNext` を別々に計算しない。
   `3*x0+1` と `3*dx` から共通の 2 を一度に剥がし、

     exponent
     next.x0
     next.dx

   を一回の走査で同時に得る。

2. `count = 1` になった family は、もはや affine family として
   追跡する必要がない。
   唯一の整数 `x0` だけを直接 odd-run で追跡する。

3. `count = 1` を専用処理するので、split によって生じていた
   `count = 0` の空 family への大量の再帰呼び出しを除去する。

4. 健全性は `familyCheck_sound` で直接証明する。
   実行用 checker が論理的な証明木全体を構築する必要はない。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh


/-!
元の外部 API と小さい補助用途のため残す。

高速な hot loop では、2本の `twoDepth` を別々に呼ぶのではなく、
下の `proposedStepAux` を使用する。
-/
def twoDepth : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x =>
      if x % 2 = 0 then
        twoDepth k (x / 2) + 1
      else
        0


/-
====================================================================
  affine family 用: 2本を同時に 2 で割る
====================================================================
-/

/--
`3*x0+1` と `3*dx` から共通の 2 の冪を剥がした結果。

`e`  : 共通に剥がした 2 の個数
`x0` : `(3*s.x0+1) / 2^e`
`dx` : `(3*s.dx)   / 2^e`

ただし実行器自身は上の割り算を改めて行わない。
剥離を進めながら結果を直接得る。
-/
structure ProposedStep where
  e  : Nat
  x0 : Nat
  dx : Nat
  deriving Repr, DecidableEq

/--
tail-recursive な共通2進剥離。

`e` は accumulator。
`x`, `dx` の両方が偶数である間だけ同時に2で割る。
-/
def proposedStepAux : Nat → Nat → Nat → Nat → ProposedStep
  | 0, e, x, dx =>
      ⟨e, x, dx⟩

  | k + 1, e, x, dx =>
      if x % 2 = 0 then
        if dx % 2 = 0 then
          proposedStepAux k (e + 1) (x / 2) (dx / 2)
        else
          ⟨e, x, dx⟩
      else
        ⟨e, x, dx⟩

/--
affine state から次の候補を一回で生成する。

従来は

  twoDepth (3*x0+1)
  twoDepth (3*dx)
  min
  2^e
  division
  division

という流れだった。

ここでは2本を同時に剥がす。
-/
def proposedStep (s : AffineOrbitState) : ProposedStep :=
  proposedStepAux 128 0 (3 * s.x0 + 1) (3 * s.dx)

/--
`ProposedStep` を affine state に戻す。
`n0`, `dn`, `count` は変化しない。
-/
def proposedState
    (s : AffineOrbitState)
    (p : ProposedStep) : AffineOrbitState :=
  { s with
      x0 := p.x0
      dx := p.dx }

/--
旧 API 互換 wrapper。

高速な `familyCheck` の内部では使わない。
-/
def proposedExponent (s : AffineOrbitState) : Nat :=
  (proposedStep s).e

/--
旧 API 互換 wrapper。

高速な `familyCheck` の内部では
`proposedStep` を一回だけ呼び、その結果を共有する。
-/
def proposedNext (s : AffineOrbitState) : AffineOrbitState :=
  proposedState s (proposedStep s)


/-
====================================================================
  count = 1 専用 checker
====================================================================
-/

/--
単一整数の accelerated odd step 候補。

`family.count = 1` になった後は `dx` を追う必要がない。
-/
structure ScalarStep where
  e : Nat
  y : Nat
  deriving Repr, DecidableEq

/--
単一整数用の tail-recursive 2進剥離。
-/
def scalarStepAux : Nat → Nat → Nat → ScalarStep
  | 0, e, x =>
      ⟨e, x⟩

  | k + 1, e, x =>
      if x % 2 = 0 then
        scalarStepAux k (e + 1) (x / 2)
      else
        ⟨e, x⟩

/--
x に対して

  3*x+1 = 2^e * y

となる候補を作る。
-/
def scalarStep (x : Nat) : ScalarStep :=
  scalarStepAux 128 0 (3 * x + 1)

/--
scalar proposal の独立検算。

generator の結果そのものを信用せず、

  e > 0
  2^e * y = 3*x+1
  y odd

を検査する。
-/
def scalarStepOK (x : Nat) (p : ScalarStep) : Prop :=
  0 < p.e ∧
    2^p.e * p.y = 3 * x + 1 ∧
    p.y % 2 = 1

instance (x : Nat) (p : ScalarStep) :
    Decidable (scalarStepOK x p) :=
  inferInstanceAs
    (Decidable
      (0 < p.e ∧
       2^p.e * p.y = 3 * x + 1 ∧
       p.y % 2 = 1))

/--
family が1要素になった後の専用検査器。

affine coefficient `dx`, `dn` を以後まったく計算しない。
-/
def singletonCheck : Nat → Nat → Nat → Bool
  | 0, _, _ =>
      false

  | fuel + 1, n0, x =>
      if x < n0 then
        true
      else
        let p := scalarStep x

        if scalarStepOK x p then
          if p.y < n0 then
            true
          else
            singletonCheck fuel n0 p.y
        else
          false


/--
`singletonCheck = true` なら、
その単一整数には fuel 以下の odd-run による降下が存在する。
-/
theorem singletonCheck_sound
    {fuel n0 x : Nat}
    (h : singletonCheck fuel n0 x = true) :
    ∃ w y,
      OddRun w x y ∧
      y < n0 ∧
      w.length ≤ fuel := by

  induction fuel generalizing x with
  | zero =>
      simp [singletonCheck] at h

  | succ fuel ih =>
      by_cases hdrop : x < n0

      · exact
          ⟨[],
           x,
           OddRun.nil x,
           hdrop,
           by simp⟩

      · let p := scalarStep x

        by_cases hok : scalarStepOK x p

        · by_cases hy : p.y < n0

          · refine
              ⟨[p.e],
               p.y,
               ?_,
               hy,
               by simp⟩

            exact
              OddRun.cons
                hok.1
                hok.2.1
                hok.2.2
                (OddRun.nil p.y)

          · have htail :
                singletonCheck fuel n0 p.y = true := by
              simpa
                [singletonCheck, hdrop, p, hok, hy]
                using h

            obtain ⟨w, z, hw, hz, hb⟩ :=
              ih htail

            refine
              ⟨p.e :: w,
               z,
               ?_,
               hz,
               ?_⟩

            · exact
                OddRun.cons
                  hok.1
                  hok.2.1
                  hok.2.2
                  hw

            · simpa using Nat.succ_le_succ hb

        · simp
            [singletonCheck, hdrop, p, hok]
            at h


/-
====================================================================
  高速 family checker
====================================================================
-/

/--
高速版 family checker。

重要な分岐順:

  count = 0
      ↓
  affine 全体が既に降下
      ↓
  count = 1
      ↓
  singletonCheck
      ↓
  count >= 2 のときだけ affine step / split

したがって `count = 1` からさらに

  evenFamily count=1
  oddFamily  count=0

へ分割し続ける無駄がない。
-/
def familyCheck : Nat → AffineOrbitState → Bool
  | 0, s =>
      s.count == 0

  | fuel + 1, s =>
      if s.count = 0 then
        true

      else if s.x0 < s.n0 ∧ s.dx ≤ s.dn then
        true

      else if s.count = 1 then
        singletonCheck (fuel + 1) s.n0 s.x0

      else
        let p := proposedStep s
        let t := proposedState s p

        if earlyOK s t p.e then
          true

        else if stepOK s t p.e then
          familyCheck fuel t

        else
          familyCheck fuel (evenFamily s) &&
          familyCheck fuel (oddFamily s)


/-
====================================================================
  familyCheck の直接健全性
====================================================================
-/

/--
`familyCheck = true` なら、
family の全候補に fuel 以下の odd-run による降下が存在する。

旧版のように実行 checker と同型の巨大な certificate tree を
別途定義する必要はない。
-/
theorem familyCheck_sound
    {fuel : Nat}
    {s : AffineOrbitState}
    (h : familyCheck fuel s = true) :
    FamilyDrops s fuel := by

  induction fuel generalizing s with

  | zero =>
      have hcount : s.count = 0 := by
        simpa [familyCheck] using h

      intro i hi
      omega

  | succ fuel ih =>

      by_cases hcount0 : s.count = 0

      · intro i hi
        omega

      · by_cases hdrop :
          s.x0 < s.n0 ∧ s.dx ≤ s.dn

        · intro i hi

          exact
            ⟨[],
             s.x0 + s.dx * i,
             OddRun.nil _,
             Nat.add_lt_add_of_lt_of_le
               hdrop.1
               (Nat.mul_le_mul_right i hdrop.2),
             by simp⟩

        · by_cases hcount1 : s.count = 1

          /-
          ----------------------------------------------------------
          singleton branch
          ----------------------------------------------------------
          -/
          · have hs :
                singletonCheck
                    (fuel + 1)
                    s.n0
                    s.x0 = true := by
              simpa
                [familyCheck,
                 hcount0,
                 hdrop,
                 hcount1]
                using h

            obtain ⟨w, y, hw, hy, hb⟩ :=
              singletonCheck_sound hs

            intro i hi

            have hi0 : i = 0 := by
              omega

            subst i

            refine ⟨w, y, ?_, ?_, hb⟩

            · simpa using hw

            · simpa using hy

          /-
          ----------------------------------------------------------
          count >= 2:
          一回だけ proposedStep を計算する
          ----------------------------------------------------------
          -/
          · let p := proposedStep s
            let t := proposedState s p

            have hcore :
                (if earlyOK s t p.e then
                   true
                 else if stepOK s t p.e then
                   familyCheck fuel t
                 else
                   familyCheck fuel (evenFamily s) &&
                   familyCheck fuel (oddFamily s)) = true := by
              simpa
                [familyCheck,
                 hcount0,
                 hdrop,
                 hcount1]
                using h

            by_cases hearly : earlyOK s t p.e

            /-
            --------------------------------------------------------
            early descent
            --------------------------------------------------------
            -/
            · rcases hearly with
                ⟨he, hx, hdx, ht0, htd⟩

              intro i hi

              have hstep :
                  2^p.e * (t.x0 + t.dx * i) =
                    3 * (s.x0 + s.dx * i) + 1 := by
                calc
                  2^p.e * (t.x0 + t.dx * i)
                      =
                    2^p.e * t.x0 +
                      (2^p.e * t.dx) * i := by
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

              have hpos :
                  0 < t.x0 + t.dx * i := by
                by_cases hz :
                    t.x0 + t.dx * i = 0

                · rw [hz, Nat.mul_zero] at hstep
                  omega

                · omega

              obtain ⟨v, y, hy, ho, hle⟩ :=
                exists_odd_factor hpos

              refine
                ⟨[p.e + v],
                 y,
                 ?_,
                 ?_,
                 by simp⟩

              · exact
                  OddRun.cons
                    (by omega)
                    (by
                      rw
                        [Nat.pow_add,
                         Nat.mul_assoc,
                         ← hy]
                      exact hstep)
                    ho
                    (OddRun.nil y)

              · exact
                  Nat.lt_of_le_of_lt
                    hle
                    (Nat.add_lt_add_of_lt_of_le
                      ht0
                      (Nat.mul_le_mul_right i htd))

            /-
            --------------------------------------------------------
            affine step
            --------------------------------------------------------
            -/
            · by_cases hstepOK : stepOK s t p.e

              · have ht :
                    familyCheck fuel t = true := by
                  simpa
                    [hearly, hstepOK]
                    using hcore

                have htail :
                    FamilyDrops t fuel :=
                  ih ht

                rcases hstepOK with
                  ⟨he,
                   hn,
                   hd,
                   hcount,
                   hx,
                   hdx,
                   ho,
                   hdo⟩

                intro i hi

                obtain ⟨w, y, hw, hy, hb⟩ :=
                  htail i (by omega)

                refine
                  ⟨p.e :: w,
                   y,
                   ?_,
                   ?_,
                   ?_⟩

                · exact
                    OddRun.cons
                      he
                      (by
                        calc
                          2^p.e *
                              (t.x0 + t.dx * i)
                              =
                            2^p.e * t.x0 +
                              (2^p.e * t.dx) * i := by
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
                                omega)
                      (by
                        simp
                          [Nat.add_mod,
                           Nat.mul_mod,
                           ho,
                           hdo])
                      hw

                · simpa [hn, hd] using hy

                · simpa using Nat.succ_le_succ hb

              /-
              ------------------------------------------------------
              split
              ------------------------------------------------------
              -/
              · have hsplit :
                    familyCheck fuel (evenFamily s) = true ∧
                    familyCheck fuel (oddFamily s) = true := by

                  have hb :
                      familyCheck fuel (evenFamily s) &&
                        familyCheck fuel (oddFamily s) = true := by
                    simpa
                      [hearly, hstepOK]
                      using hcore

                  --exact Bool.and_eq_true.mp hb
                  constructor
                  · have := hb
                    simp only [Bool.and_eq_true] at this
                    exact this.1
                  · have := hb
                    simp only [Bool.and_eq_true] at this
                    simpa using this.2

                have hleft :
                    FamilyDrops (evenFamily s) fuel :=
                  ih hsplit.1

                have hright :
                    FamilyDrops (oddFamily s) fuel :=
                  ih hsplit.2

                intro i hi

                rcases index_partition i s.count hi with
                  hEven | hOdd

                /-
                even index
                -/
                · obtain ⟨w, y, hw, hy, hb⟩ :=
                    hleft
                      (i / 2)
                      hEven.2.1

                  have hx :
                      s.x0 + s.dx * i =
                        (evenFamily s).x0 +
                          (evenFamily s).dx * (i / 2) := by
                    calc
                      s.x0 + s.dx * i
                          =
                        s.x0 +
                          s.dx * (2 * (i / 2)) := by
                            exact
                              congrArg
                                (fun z =>
                                  s.x0 + s.dx * z)
                                hEven.2.2

                      _ =
                        (evenFamily s).x0 +
                          (evenFamily s).dx *
                            (i / 2) := by
                              simp
                                [evenFamily,
                                 Nat.mul_left_comm,
                                 Nat.mul_comm]

                  have hn :
                      s.n0 + s.dn * i =
                        (evenFamily s).n0 +
                          (evenFamily s).dn * (i / 2) := by
                    calc
                      s.n0 + s.dn * i
                          =
                        s.n0 +
                          s.dn * (2 * (i / 2)) := by
                            exact
                              congrArg
                                (fun z =>
                                  s.n0 + s.dn * z)
                                hEven.2.2

                      _ =
                        (evenFamily s).n0 +
                          (evenFamily s).dn *
                            (i / 2) := by
                              simp
                                [evenFamily,
                                 Nat.mul_left_comm,
                                 Nat.mul_comm]

                  exact
                    ⟨w,
                     y,
                     hx ▸ hw,
                     hn ▸ hy,
                     Nat.le_trans
                       hb
                       (Nat.le_succ fuel)⟩

                /-
                odd index
                -/
                · obtain ⟨w, y, hw, hy, hb⟩ :=
                    hright
                      (i / 2)
                      hOdd.2.1

                  have hx :
                      s.x0 + s.dx * i =
                        (oddFamily s).x0 +
                          (oddFamily s).dx * (i / 2) := by
                    calc
                      s.x0 + s.dx * i
                          =
                        s.x0 +
                          s.dx *
                            (2 * (i / 2) + 1) := by
                              exact
                                congrArg
                                  (fun z =>
                                    s.x0 + s.dx * z)
                                  hOdd.2.2

                      _ =
                        (oddFamily s).x0 +
                          (oddFamily s).dx *
                            (i / 2) := by
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
                      s.n0 + s.dn * i
                          =
                        s.n0 +
                          s.dn *
                            (2 * (i / 2) + 1) := by
                              exact
                                congrArg
                                  (fun z =>
                                    s.n0 + s.dn * z)
                                  hOdd.2.2

                      _ =
                        (oddFamily s).n0 +
                          (oddFamily s).dn *
                            (i / 2) := by
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
                     Nat.le_trans
                       hb
                       (Nat.le_succ fuel)⟩


/-
====================================================================
  高枝 root family
====================================================================
-/

def rootFamily (a : Nat) : AffineOrbitState :=
  {
    n0 := 3 * branchResidue a + 1
    dn := 3 * branchModulus a

    x0 := 3 * branchResidue a + 1
    dx := 3 * branchModulus a

    count := branchCount a
  }


end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
