import FiniteQuantumSL2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def qFalling (q : K) (k : ℤ) : ℕ → K
  | 0 => 1
  | m+1 => qFalling q k m*qInteger q (k-m)

theorem quantumE_power_single (q : K) (k : ℤ) (a : K) (m : ℕ) :
    ((quantumE q)^m) (Finsupp.single k a)=Finsupp.single (k-m) (a*qFalling q k m) := by
  induction m with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.cast_zero,sub_zero,qFalling,mul_one]
  | succ m ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    simp only [quantumE,weightShift_single,qFalling]
    have hi : k-(m:ℤ)+(-1)=k-(m+1:ℕ) := by omega
    rw [hi]
    congr 1
    ring

theorem quantumF_power_single (q : K) (l k : ℤ) (a : K) (m : ℕ) :
    ((quantumF q l)^m) (Finsupp.single k a)=Finsupp.single (k+m) (a*qFalling q (l-k) m) := by
  induction m with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.cast_zero,add_zero,qFalling,mul_one]
  | succ m ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    simp only [quantumF,weightShift_single,qFalling]
    have hi : k+(m:ℤ)+1=k+(m+1:ℕ) := by omega
    have hj : l-(k+(m:ℤ))=l-k-m := by omega
    rw [hi,hj]
    congr 1
    ring

theorem qFalling_zero (q : K) (k : ℤ) (m : ℕ) (hk : 0≤k) (hm : k<m) :
    qFalling q k m=0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [qFalling]
    by_cases he : k=(m:ℤ)
    · rw [he,sub_self,qInteger_zero,mul_zero]
    · rw [ih (by omega),zero_mul]

theorem qFalling_ne_zero (q : K) (k : ℤ) (m : ℕ) (hm : (m:ℤ)≤k)
    (hq : ∀ j : ℤ,0<j → j≤k → qInteger q j≠0) : qFalling q k m≠0 := by
  induction m with
  | zero => exact one_ne_zero
  | succ m ih =>
    rw [qFalling]
    exact mul_ne_zero (ih (by omega)) (hq (k-m) (by omega) (by omega))

theorem quantumE_power_kills_lower (q : K) (k : ℤ) (a : K) (m : ℕ)
    (hk : 0≤k) (hm : k<m) : ((quantumE q)^m) (Finsupp.single k a)=0 := by
  rw [quantumE_power_single,qFalling_zero q k m hk hm,mul_zero,Finsupp.single_zero]

theorem end_power_preserves {V : Type*} [AddCommGroup V] [Module K V]
    (S : Submodule K V) (T : Module.End K V) (hT : ∀ v∈S,T v∈S)
    (v : V) (hv : v∈S) (m : ℕ) : (T^m) v∈S := by
  induction m with
  | zero => exact hv
  | succ m ih => rw [pow_succ',Module.End.mul_apply]; exact hT _ ih

theorem quantumE_power_top (q : K) (p : WeightModule K) (m : ℕ)
    (hp : ∀ k∈p.support,0≤k ∧ k≤(m:ℤ)) :
    ((quantumE q)^m) p=Finsupp.single 0 (p m*qFalling q m m) := by
  classical
  calc
    ((quantumE q)^m) p=
        ∑ k∈p.support,((quantumE q)^m) (Finsupp.single k (p k)) := by
      conv_lhs => rw [← Finsupp.sum_single p]
      rw [Finsupp.sum,map_sum]
    _=((quantumE q)^m) (Finsupp.single (m:ℤ) (p m)) := by
      apply Finset.sum_eq_single (m:ℤ)
      · intro k hk hkm
        exact quantumE_power_kills_lower q k (p k) m (hp k hk).1 (by have := (hp k hk).2; omega)
      · intro hm
        rw [Finsupp.notMem_support_iff.mp hm,Finsupp.single_zero,map_zero]
    _=_ := by rw [quantumE_power_single,sub_self]

end AMSPhysical

#print axioms AMSPhysical.quantumE_power_single
#print axioms AMSPhysical.quantumF_power_single
