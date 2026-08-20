import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLargeMReduction

set_option linter.style.nativeDecide false

/-!
# Pure B single-corner: Stage 5 executable finite arithmetic

single-corner rigidity では profile は `(m,b,c)` だけで一意に決まる。

  * `0 <= k < b` : p_k = beta_k
  * `b <= k < c`: p_k = beta_b - 1 + (k-b)
  * `c <= k < m`: p_k = beta_k
  * H = beta_m + 1

入口では `beta_b = beta_(b-1)+2` が必要。

このファイルでは finite side を parity word 全体の再構成ではなく、上の三つの区間から得る
closed affine numerator で直接走査する。

critical prefix numeratorを

  Psi_0 = 0,
  Psi_(r+1) = 3 Psi_r + 2^beta_r

とすると single-corner affine numerator は

  A(m,b,c)
    = 3^(m-b) Psi_b
      + 2^(beta_b-1) 3^(m-c) (3^(c-b)-2^(c-b))
      + (Psi_m - 3^(m-c) Psi_c).

canonical representative は

  R = -A * 3^(-m) mod 2^H

で、safety は division-free に

  A < (2^H-3^m) R

を検査する。

`singleCornerFiniteModelCheck500` はこの pure arithmetic model の exact native check。
actual `MinimalActualABObstructionPacket` へ使うには、後続 assembly で
`SingleCornerFiniteModelBridge` を供給する。これにより「計算」と「actual-to-model bridge」を
混同しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. executable critical Beatty/Psi table -/

/--
entry `k` は `(beta_k, Psi_k)` を保持する executable table。
`N` を渡すと index `0..N` を持つ。
-/
def singleCornerCriticalData : ℕ → Array (ℕ × ℕ)
  | 0 => #[(0, 0)]
  | n + 1 =>
      let D := singleCornerCriticalData n
      let q := (D[n]!).1
      let psi := (D[n]!).2
      let qNext :=
        if 3 ^ (n + 1) ≤ 2 ^ (q + 2) then q + 1 else q + 2
      let psiNext := 3 * psi + 2 ^ q
      D.push (qNext, psiNext)

/-- table から executable Beatty index を読む。 -/
def singleCornerBetaAt
    (D : Array (ℕ × ℕ))
    (k : ℕ) : ℕ :=
  (D[k]!).1

/-- table から executable critical prefix numerator を読む。 -/
def singleCornerPsiAt
    (D : Array (ℕ × ℕ))
    (k : ℕ) : ℕ :=
  (D[k]!).2

/-! ## 2. closed single-corner arithmetic model -/

/-- terminal depth `H = beta_m + 1`。 -/
def singleCornerModelH
    (D : Array (ℕ × ℕ))
    (m : ℕ) : ℕ :=
  singleCornerBetaAt D m + 1

/--
closed affine numerator `A(m,b,c)`。

finite scanner は `1 <= b < c <= m` だけで呼ぶ。
-/
def singleCornerModelAffine
    (D : Array (ℕ × ℕ))
    (m b c : ℕ) : ℕ :=
  let betaB := singleCornerBetaAt D b
  let psiB := singleCornerPsiAt D b
  let psiC := singleCornerPsiAt D c
  let psiM := singleCornerPsiAt D m
  let n := c - b
  let s := m - c
  3 ^ (m - b) * psiB +
    2 ^ (betaB - 1) * 3 ^ s * (3 ^ n - 2 ^ n) +
    (psiM - 3 ^ s * psiC)

/-- terminal contracting gap `G = 2^H - 3^m`。 -/
def singleCornerModelGap
    (D : Array (ℕ × ℕ))
    (m : ℕ) : ℕ :=
  2 ^ singleCornerModelH D m - 3 ^ m

/--
canonical positive residue `R`。
`invThreePow H m` は既存の certified `3^(-m)` in `ZMod (2^H)`。
-/
def singleCornerModelRepresentative
    (D : Array (ℕ × ℕ))
    (m b c : ℕ) : ℕ :=
  let H := singleCornerModelH D m
  let A := singleCornerModelAffine D m b c
  ((-(A : ZMod (2 ^ H))) * invThreePow H m).val

/--
model safety。これは real division を使わない exact fixed-point inequality。
-/
def SingleCornerModelSafe
    (D : Array (ℕ × ℕ))
    (m b c : ℕ) : Prop :=
  singleCornerModelAffine D m b c <
    singleCornerModelGap D m *
      singleCornerModelRepresentative D m b c

/-- executable Bool wrapper。 -/
def singleCornerModelSafeBool
    (D : Array (ℕ × ℕ))
    (m b c : ℕ) : Bool :=
  decide (
    singleCornerModelAffine D m b c <
      singleCornerModelGap D m *
        singleCornerModelRepresentative D m b c
  )

/-- single-corner entrance `beta_b-beta_(b-1)=2` の executable test。 -/
def singleCornerEntranceBool
    (D : Array (ℕ × ℕ))
    (b : ℕ) : Bool :=
  if b = 0 then false
  else decide
    (singleCornerBetaAt D b =
      singleCornerBetaAt D (b - 1) + 2)

/-! **## 3. fast finite scanner** -/

/--
`1, a, a^2, ..., a^N` を保持する power table。

scanner の inner loop から `Nat.pow` を完全に追い出すために使う。
-/
def singleCornerPowerData
    (a : ℕ) : ℕ → Array ℕ
  | 0 =>
      #[1]
  | n + 1 =>
      let D := singleCornerPowerData a n
      D.push (D[n]! * a)
/--
固定 `m` の entrance `b` に関する前計算 entry。

`constA` は

  3^(m-b) * (Psi_b + 2^(beta_b-1)) + Psi_m

`constResidue` はその `3^(-m)` 倍 modulo `2^H`。
-/
structure SingleCornerFastBEntry where
  entrance : Bool
  constA : ℕ
  constResidue : ℕ
deriving Inhabited


/--
`x,y < modulus` を仮定した一回減算型 modular addition。

scanner 内部では invariant によりこの前提が成立する。
-/
def singleCornerModAdd
    (modulus x y : ℕ) : ℕ :=
  let z := x + y
  if modulus ≤ z then
    z - modulus
  else
    z


/--
`x,y < modulus` を仮定した modular subtraction。
-/
def singleCornerModSub
    (modulus x y : ℕ) : ℕ :=
  if y ≤ x then
    x - y
  else
    modulus - (y - x)


/--
`3^(-c) mod modulus`, `c = 0..m` の table。

`inv3 = 3^(-1) mod modulus` から乗算 recurrence で生成する。
-/
def singleCornerInvThreeDataAux
    (modulus inv3 : ℕ)
    (fuel cur : ℕ)
    (acc : Array ℕ) : Array ℕ :=
  match fuel with
  | 0 =>
      acc
  | r + 1 =>
      let next :=
        (cur * inv3) % modulus
      singleCornerInvThreeDataAux
        modulus inv3
        r next
        (acc.push next)


/--
`3^(-c) mod modulus`, `0 <= c <= m`。
-/
def singleCornerInvThreeData
    (modulus inv3 m : ℕ) : Array ℕ :=
  singleCornerInvThreeDataAux
    modulus inv3
    m 1 #[1]


/--
固定 `m` の全 `b` について、

- entrance か
- closed affine の fixed `(m,b)` 部分
- その `3^(-m)` residue

を一度だけ計算する。
-/
def singleCornerBuildBDataAux
    (D : Array (ℕ × ℕ))
    (pow2 pow3 : Array ℕ)
    (m psiM modulus inv3m : ℕ)
    (b fuel : ℕ)
    (acc : Array SingleCornerFastBEntry) :
    Array SingleCornerFastBEntry :=
  match fuel with
  | 0 =>
      acc
  | r + 1 =>
      let entry :=
        if singleCornerEntranceBool D b then
          let betaB :=
            singleCornerBetaAt D b
          let psiB :=
            singleCornerPsiAt D b
          let constA :=
            pow3[m - b]! *
                (psiB + pow2[betaB - 1]!) +
              psiM
          let constResidue :=
            ((constA % modulus) * inv3m) % modulus
          {
            entrance := true
            constA := constA
            constResidue := constResidue
          }
        else
          {
            entrance := false
            constA := 0
            constResidue := 0
          }
      singleCornerBuildBDataAux
        D pow2 pow3
        m psiM modulus inv3m
        (b + 1) r
        (acc.push entry)


/--
index `b = 0..m-1` の fixed-b data。
-/
def singleCornerBuildBData
    (D : Array (ℕ × ℕ))
    (pow2 pow3 : Array ℕ)
    (m psiM modulus inv3m : ℕ) :
    Array SingleCornerFastBEntry :=
  singleCornerBuildBDataAux
    D pow2 pow3
    m psiM modulus inv3m
    0 m #[]


/--
固定 `(m,c)` のもとで `b < c` を走査する。

重要：
inner candidate では arbitrary modular multiplication をしない。

entrance が一つ進むごとに

  d_b = beta_b - b - 1

が 1 増えるので、

  2^d

の効果は単なる modular doubling で更新できる。
-/
def singleCornerFiniteModelCheckBForCFast
    (B : Array SingleCornerFastBEntry)
    (modulus gap tailPsi : ℕ)
    (b fuel powTerm residueTerm baseResidue : ℕ) :
    Bool :=
  match fuel with
  | 0 =>
      true
  | r + 1 =>
      let E := B[b]!
      if E.entrance then
        /-
        tail =
          3^(m-c) * Psi_c
          +
          3^(m-c) * 2^c * 2^d
        -/
        let tail :=
          tailPsi + powTerm
        let A :=
          E.constA - tail
        /-
        3^(-c) * (Psi_c + 2^(c+d))
        modulo 2^H
        -/
        let positiveResidue :=
          singleCornerModAdd
            modulus
            baseResidue
            residueTerm
        /-
        R =
          positiveResidue
          -
          constA * 3^(-m)
          modulo 2^H
        -/
        let R :=
          singleCornerModSub
            modulus
            positiveResidue
            E.constResidue
        if decide (A < gap * R) then
          /-
          次の entrance では d -> d+1。
          exact term は doubling。
          residue term も modular doubling。
          -/
          let powTermNext :=
            powTerm + powTerm
          let residueTermNext :=
            singleCornerModAdd
              modulus
              residueTerm
              residueTerm
          singleCornerFiniteModelCheckBForCFast
            B
            modulus gap tailPsi
            (b + 1) r
            powTermNext
            residueTermNext
            baseResidue
        else
          false
      else
        /-
        entrance でない b では d は進めない。
        -/
        singleCornerFiniteModelCheckBForCFast
          B
          modulus gap tailPsi
          (b + 1) r
          powTerm
          residueTerm
          baseResidue

/--
固定 `m` で `c = 2, ..., m` を走査する。

各 `c` について、

- `Psi_c`
- `3^(-c) mod 2^H`
- `3^(-c) * Psi_c mod 2^H`
- `3^(-c) * 2^c mod 2^H`
- `3^(m-c) * Psi_c`
- `3^(m-c) * 2^c`

を一度だけ計算し、その後の `b` 走査で再利用する。
-/
def singleCornerFiniteModelCheckCLoopFast
    (D : Array (ℕ × ℕ))
    (B : Array SingleCornerFastBEntry)
    (inv3Data pow2 pow3 : Array ℕ)
    (modulus gap m : ℕ)
    (c fuel : ℕ) : Bool :=
  match fuel with
  | 0 =>
      true
  | r + 1 =>
      let psiC :=
        singleCornerPsiAt D c
      let inv3c :=
        inv3Data[c]!
      /-
      3^(-c) * Psi_c mod 2^H
      -/
      let baseResidue :=
        ((psiC % modulus) * inv3c) % modulus
      /-
      3^(-c) * 2^c mod 2^H
      -/
      let residueTerm :=
        (pow2[c]! * inv3c) % modulus
      /-
      3^(m-c) * Psi_c
      -/
      let tailPsi :=
        pow3[m - c]! * psiC
      /-
      最初の entrance 用の exact 2-power term。

      d = 0 から開始するので

        3^(m-c) * 2^c
      -/
      let powTerm :=
        pow3[m - c]! * pow2[c]!
      let ok :=
        singleCornerFiniteModelCheckBForCFast
          B
          modulus
          gap
          tailPsi
          1
          (c - 1)
          powTerm
          residueTerm
          baseResidue
      if ok then
        singleCornerFiniteModelCheckCLoopFast
          D
          B
          inv3Data
          pow2
          pow3
          modulus
          gap
          m
          (c + 1)
          r
      else
        false

/--
fixed `m` scanner。

`m` ごとに

- `H = beta_m + 1`
- modulus `2^H`
- gap `2^H - 3^m`
- `Psi_m`
- `3^(-c)` table
- fixed-b table

を一度だけ構成する。
-/
def singleCornerFiniteModelCheckAtFast
    (D : Array (ℕ × ℕ))
    (pow2 pow3 : Array ℕ)
    (m : ℕ) : Bool :=
  if m < 3 then
    true
  else
    let H :=
      singleCornerBetaAt D m + 1
    let modulus :=
      pow2[H]!
    let threeM :=
      pow3[m]!
    let gap :=
      modulus - threeM
    let psiM :=
      singleCornerPsiAt D m
    /-
    3^(-1) mod 2^H。
    -/
    let inv3 :=
      (invThreePow H 1).val
    /-
    3^(-c) mod 2^H, c = 0,...,m
    を recurrence で一度だけ作る。
    -/
    let inv3Data :=
      singleCornerInvThreeData
        modulus
        inv3
        m
    /-
    3^(-m) mod 2^H。
    -/
    let inv3m :=
      inv3Data[m]!
    /-
    fixed `(m,b)` quantity を全 b について前計算。
    -/
    let B :=
      singleCornerBuildBData
        D
        pow2
        pow3
        m
        psiM
        modulus
        inv3m
    /-
    c = 2,...,m を走査。

    start = 2
    fuel = m - 1

    なので実際の c は
      2, 3, ..., m
    となる。
    -/
    singleCornerFiniteModelCheckCLoopFast
      D
      B
      inv3Data
      pow2
      pow3
      modulus
      gap
      m
      2
      (m - 1)

/--
`m = start,...,start+fuel-1`。
-/
def singleCornerFiniteModelCheckMLoopFast
    (D : Array (ℕ × ℕ))
    (pow2 pow3 : Array ℕ)
    (start fuel : ℕ) : Bool :=
  match fuel with
  | 0 =>
      true
  | r + 1 =>
      if singleCornerFiniteModelCheckAtFast
          D pow2 pow3 start
      then
        singleCornerFiniteModelCheckMLoopFast
          D pow2 pow3
          (start + 1) r
      else
        false


/--
`m < M0` の高速 exact scanner。
-/
def singleCornerFiniteModelCheckBelow
    (M0 : ℕ) : Bool :=
  let D :=
    singleCornerCriticalData M0
  let pow2 :=
    singleCornerPowerData
      2 (2 * M0 + 2)
  let pow3 :=
    singleCornerPowerData
      3 M0
  singleCornerFiniteModelCheckMLoopFast
    D pow2 pow3
    0 M0


theorem singleCornerFiniteModelCheck64 :
    singleCornerFiniteModelCheckBelow 64 = true := by
  native_decide

/- O(M^3)は通ったけど重すぎるから通ったものとする
theorem singleCornerFiniteModelCheck500 :
    singleCornerFiniteModelCheckBelow 501 = true := by
  native_decide

-/
/--
`lo ≤ m < hi` の single-corner model tuple を exact に走査する。

各区間 theorem を独立に native compilation できるように、
必要な critical/power table もこの区間の上端 `hi` までだけ構成する。
-/
def singleCornerFiniteModelCheckRange
    (lo hi : ℕ) : Bool :=
  if hi ≤ lo then
    true
  else
    let D :=
      singleCornerCriticalData hi
    let pow2 :=
      singleCornerPowerData
        2 (2 * hi + 2)
    let pow3 :=
      singleCornerPowerData
        3 hi
    singleCornerFiniteModelCheckMLoopFast
      D pow2 pow3
      lo (hi - lo)

/-! **## 4. frozen finite certificates** -/

/--
`0 ≤ m < 100` の exact finite certificate。
-/
theorem singleCornerFiniteModelCheck_000_099 :
    singleCornerFiniteModelCheckRange 0 100 = true := by
  native_decide


/--
`100 ≤ m < 200` の exact finite certificate。
-/
theorem singleCornerFiniteModelCheck_100_199 :
    singleCornerFiniteModelCheckRange 100 200 = true := by
  native_decide


/--
`200 ≤ m < 300` の exact finite certificate。
-/
theorem singleCornerFiniteModelCheck_200_299 :
    singleCornerFiniteModelCheckRange 200 300 = true := by
  native_decide


/--
`300 ≤ m < 400` の exact finite certificate。
-/
theorem singleCornerFiniteModelCheck_300_399 :
    singleCornerFiniteModelCheckRange 300 400 = true := by
  native_decide


/--
`400 ≤ m < 450` の exact finite certificate。
-/
theorem singleCornerFiniteModelCheck_400_450 :
    singleCornerFiniteModelCheckRange 400 450  = true := by
  native_decide

/--
`450 ≤ m ≤ 500`、すなわち `450 ≤ m < 501`
の exact finite certificate。
-/
theorem singleCornerFiniteModelCheck_450_500 :
    singleCornerFiniteModelCheckRange 450 501 = true := by
  native_decide

/--
`m ≤ 500` を構成する6個の独立 native certificate。
数学的な証明で各区間を取り出すための Prop-level bundle。
-/
theorem singleCornerFiniteModelCheck500Certificates :
    singleCornerFiniteModelCheckRange 0 100 = true ∧
    singleCornerFiniteModelCheckRange 100 200 = true ∧
    singleCornerFiniteModelCheckRange 200 300 = true ∧
    singleCornerFiniteModelCheckRange 300 400 = true ∧
    singleCornerFiniteModelCheckRange 400 450 = true ∧
    singleCornerFiniteModelCheckRange 450 501 = true := by
  exact ⟨
    singleCornerFiniteModelCheck_000_099,
    singleCornerFiniteModelCheck_100_199,
    singleCornerFiniteModelCheck_200_299,
    singleCornerFiniteModelCheck_300_399,
    singleCornerFiniteModelCheck_400_450,
    singleCornerFiniteModelCheck_450_500
  ⟩


/--
500 cutoff 用の executable Bool。

重い一枚岩 scan は行わず、
6個の frozen range check を Bool conjunction で束ねる。
-/
def singleCornerFiniteModelCheck500Chunks : Bool :=
  singleCornerFiniteModelCheckRange 0 100 &&
  singleCornerFiniteModelCheckRange 100 200 &&
  singleCornerFiniteModelCheckRange 200 300 &&
  singleCornerFiniteModelCheckRange 300 400 &&
  singleCornerFiniteModelCheckRange 400 450 &&
  singleCornerFiniteModelCheckRange 450 501


/--
6個の frozen certificate から executable Bool が true と分かる。

ここでは `native_decide` を再実行しない。
-/
theorem singleCornerFiniteModelCheck500Chunks_ok :
    singleCornerFiniteModelCheck500Chunks = true := by
  simp [
    singleCornerFiniteModelCheck500Chunks,
    singleCornerFiniteModelCheck_000_099,
    singleCornerFiniteModelCheck_100_199,
    singleCornerFiniteModelCheck_200_299,
    singleCornerFiniteModelCheck_300_399,
    singleCornerFiniteModelCheck_400_450,
    singleCornerFiniteModelCheck_450_500
  ]



end ExternalArithmetic
end CSTMicro
end Collatz2
