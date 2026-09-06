/-!
affine familyの検査用の独立した核。
外部generatorが選んだ指数・子stateを等式として再検査する。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

inductive OddRun : List Nat → Nat → Nat → Prop where
  | nil (x : Nat) : OddRun [] x x
  | cons {e x y z : Nat} {w : List Nat}
      (positive : 0 < e) (equation : 2^e*y = 3*x+1)
      (odd : y % 2 = 1) (tail : OddRun w y z) : OddRun (e::w) x z

structure AffineOrbitState where
  n0 : Nat
  dn : Nat
  x0 : Nat
  dx : Nat
  count : Nat
  deriving Repr, DecidableEq

def FamilyDrops (s : AffineOrbitState) (bound : Nat) : Prop :=
  ∀ i, i < s.count → ∃ w y, OddRun w (s.x0+s.dx*i) y ∧
    y < s.n0+s.dn*i ∧ w.length ≤ bound

inductive AffineCertificate where
  | empty
  | drop
  | step (e : Nat) (next : AffineOrbitState) (tail : AffineCertificate)
  | early (e : Nat) (next : AffineOrbitState)
  | split (left right : AffineCertificate)
  deriving Repr

def AffineCertificate.bound : AffineCertificate → Nat
  | .empty | .drop => 0
  | .step _ _ c => c.bound+1
  | .early _ _ => 1
  | .split l r => max l.bound r.bound

def evenFamily (s : AffineOrbitState) : AffineOrbitState :=
  { n0 := s.n0, dn := 2*s.dn, x0 := s.x0, dx := 2*s.dx,
    count := (s.count+1)/2 }
def oddFamily (s : AffineOrbitState) : AffineOrbitState :=
  { n0 := s.n0+s.dn, dn := 2*s.dn, x0 := s.x0+s.dx, dx := 2*s.dx,
    count := s.count/2 }

def stepOK (s t : AffineOrbitState) (e : Nat) : Prop :=
  0 < e ∧ t.n0=s.n0 ∧ t.dn=s.dn ∧ t.count=s.count ∧
  2^e*t.x0=3*s.x0+1 ∧ 2^e*t.dx=3*s.dx ∧ t.x0%2=1 ∧ t.dx%2=0
instance (s t : AffineOrbitState) (e : Nat) : Decidable (stepOK s t e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- 途中の偶数値ですでに降下すれば、その奇数部分も降下している。 -/
def earlyOK (s t : AffineOrbitState) (e : Nat) : Prop :=
  0<e ∧ 2^e*t.x0=3*s.x0+1 ∧ 2^e*t.dx=3*s.dx ∧
  t.x0<s.n0 ∧ t.dx≤s.dn
instance (s t : AffineOrbitState) (e : Nat) : Decidable (earlyOK s t e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem exists_odd_factor {n : Nat} (hn : 0 < n) :
    ∃ e y, n=2^e*y ∧ y%2=1 ∧ y≤n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases ho : n%2=1
    · exact ⟨0,n,by simp,ho,Nat.le_refl _⟩
    · have hd : 0<n/2 := by omega
      have hlt : n/2<n := by omega
      obtain ⟨e,y,he,hy,hyn⟩ := ih (n/2) hlt hd
      refine ⟨e+1,y,?_,hy,by omega⟩
      calc
        n = 2*(n/2) := by omega
        _ = 2*(2^e*y) := by rw [he]
        _ = 2^(e+1)*y := by simp [Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm]

def verifyAffine (s : AffineOrbitState) : AffineCertificate → Bool
  | .empty => s.count == 0
  | .drop => decide (s.x0 < s.n0 ∧ s.dx ≤ s.dn)
  | .step e t c => decide (stepOK s t e) && verifyAffine t c
  | .early e t => decide (earlyOK s t e)
  | .split l r => verifyAffine (evenFamily s) l && verifyAffine (oddFamily s) r

/-- 偶数番と奇数番の子は親の全indexを一意に表す。 -/
theorem index_partition (i N : Nat) (hi : i < N) :
    (i%2=0 ∧ i/2 < (N+1)/2 ∧ i=2*(i/2)) ∨
    (i%2=1 ∧ i/2 < N/2 ∧ i=2*(i/2)+1) := by omega

theorem split_disjoint (i j : Nat) : 2*i ≠ 2*j+1 := by omega

theorem verifyAffine_sound (c : AffineCertificate) (s : AffineOrbitState)
    (hc : verifyAffine s c = true) : FamilyDrops s c.bound := by
  induction c generalizing s with
  | empty =>
    simp [verifyAffine] at hc
    intro i hi
    omega
  | drop =>
    simp only [verifyAffine, decide_eq_true_eq] at hc
    intro i _
    exact ⟨[], s.x0+s.dx*i, .nil _,
      Nat.add_lt_add_of_lt_of_le hc.1 (Nat.mul_le_mul_right i hc.2), by simp [AffineCertificate.bound]⟩
  | step e t c ih =>
    simp only [verifyAffine, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc.1 with ⟨he, hn, hd, hcount, hx, hdx, ho, hdo⟩
    intro i hi
    obtain ⟨w,y,hw,hy,hb⟩ := ih t hc.2 i (by omega)
    refine ⟨e::w,y,.cons he ?_ ?_ hw, ?_, ?_⟩
    · calc
        2^e*(t.x0+t.dx*i) = 2^e*t.x0+(2^e*t.dx)*i := by
          simp only [Nat.mul_add, Nat.mul_assoc]
        _ = 3*s.x0+1+(3*s.dx)*i := by rw [hx,hdx]
        _ = 3*(s.x0+s.dx*i)+1 := by
          simp only [Nat.mul_add, Nat.mul_assoc]; omega
    · simp [Nat.add_mod, Nat.mul_mod, ho, hdo]
    · simpa [hn,hd] using hy
    · simpa [AffineCertificate.bound] using Nat.add_le_add_right hb 1
  | early e t =>
    simp only [verifyAffine,decide_eq_true_eq] at hc
    rcases hc with ⟨he,hx,hdx,ht0,htd⟩
    intro i _
    have hstep : 2^e*(t.x0+t.dx*i)=3*(s.x0+s.dx*i)+1 := by
      calc
        _ = 2^e*t.x0+(2^e*t.dx)*i := by simp only [Nat.mul_add,Nat.mul_assoc]
        _ = 3*s.x0+1+(3*s.dx)*i := by rw [hx,hdx]
        _ = _ := by simp only [Nat.mul_add,Nat.mul_assoc]; omega
    have hpos : 0<t.x0+t.dx*i := by
      by_cases hz : t.x0+t.dx*i=0
      · rw [hz,Nat.mul_zero] at hstep
        omega
      · omega
    obtain ⟨v,y,hy,ho,hle⟩ := exists_odd_factor hpos
    refine ⟨[e+v],y,.cons (by omega) ?_ ho (.nil _),?_,by simp [AffineCertificate.bound]⟩
    · rw [Nat.pow_add,Nat.mul_assoc,←hy]; exact hstep
    · exact Nat.lt_of_le_of_lt hle
        (Nat.add_lt_add_of_lt_of_le ht0 (Nat.mul_le_mul_right i htd))
  | split l r ihl ihr =>
    simp only [verifyAffine, Bool.and_eq_true] at hc
    intro i hi
    rcases index_partition i s.count hi with h | h
    · obtain ⟨w,y,hw,hy,hb⟩ := ihl (evenFamily s) hc.1 (i/2) h.2.1
      have hx : s.x0+s.dx*i = (evenFamily s).x0+(evenFamily s).dx*(i/2) := by
        calc
          _ = s.x0+s.dx*(2*(i/2)) := congrArg (fun z => s.x0+s.dx*z) h.2.2
          _ = _ := by simp [evenFamily,Nat.mul_left_comm,Nat.mul_comm]
      have hn : s.n0+s.dn*i = (evenFamily s).n0+(evenFamily s).dn*(i/2) := by
        calc
          _ = s.n0+s.dn*(2*(i/2)) := congrArg (fun z => s.n0+s.dn*z) h.2.2
          _ = _ := by simp [evenFamily,Nat.mul_left_comm,Nat.mul_comm]
      exact ⟨w,y,hx ▸ hw,hn ▸ hy, Nat.le_trans hb (Nat.le_max_left _ _)⟩
    · obtain ⟨w,y,hw,hy,hb⟩ := ihr (oddFamily s) hc.2 (i/2) h.2.1
      have hx : s.x0+s.dx*i = (oddFamily s).x0+(oddFamily s).dx*(i/2) := by
        calc
          _ = s.x0+s.dx*(2*(i/2)+1) := congrArg (fun z => s.x0+s.dx*z) h.2.2
          _ = _ := by simp [oddFamily,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc,Nat.add_comm]
      have hn : s.n0+s.dn*i = (oddFamily s).n0+(oddFamily s).dn*(i/2) := by
        calc
          _ = s.n0+s.dn*(2*(i/2)+1) := congrArg (fun z => s.n0+s.dn*z) h.2.2
          _ = _ := by simp [oddFamily,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc,Nat.add_comm]
      exact ⟨w,y,hx ▸ hw,hn ▸ hy, Nat.le_trans hb (Nat.le_max_right _ _)⟩

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
