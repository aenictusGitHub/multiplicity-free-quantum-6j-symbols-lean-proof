import QuantumClebschLast

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem finiteQuantumE_power_forget (q : ℝ) (L a : ℕ) (p : RealQuantumSpace L) :
    (((finiteQuantumE q L)^a) p).val=((quantumE q)^a) p.val := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [pow_succ',Module.End.mul_apply]
    change quantumE q ((((finiteQuantumE q L)^a) p).val)=quantumE q (((quantumE q)^a) p.val)
    rw [ih]

def loweredWeightIndex (L : ℕ) (a : Fin (L+1)) (y : ℕ) : Fin (L+1) :=
  ⟨a.val-y,by have hh := a.isLt;omega⟩

theorem standardWeightBasis_E_power (q : ℝ) (L : ℕ) (a : Fin (L+1)) (y : ℕ) (hy : y≤a.val) :
    ((finiteQuantumE q L)^y) (standardWeightBasis L a)=
      qFalling q a.val y • standardWeightBasis L (loweredWeightIndex L a y) := by
  apply Subtype.ext
  rw [finiteQuantumE_power_forget]
  simp only [standardWeightBasis_apply]
  change ((quantumE q)^y) (Finsupp.single (a.val:ℤ) (1:ℝ))=
    (qFalling q a.val y • Finsupp.single (((a.val-y:ℕ):ℤ)) (1:ℝ))
  rw [quantumE_power_single,Finsupp.smul_single,smul_eq_mul,one_mul,mul_one]
  congr 1
  omega

/-- All other tensor E terms vanish at the last weight of the second factor. -/
theorem finiteTensor_E_power_last_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m a : ℕ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) :
    finiteTensorCoefficient l m 0 m
      (((finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 0))^a) p)=
      q^(-(m:ℤ)*(a:ℤ))*qfactorial q a*finiteTensorCoefficient l m a m p := by
  induction a generalizing p with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.cast_zero,mul_zero,zpow_zero,qfactorial_zero,one_mul]
  | succ a ih =>
    rw [pow_succ,Module.End.mul_apply,ih,
      finiteTensor_E_coefficient q hq hq1 l m a m,
      finiteTensorCoefficient_outside_right l m a ((m:ℤ)+1) _ (Or.inr (by omega)),mul_zero,add_zero]
    have hphase : q^(-(m:ℤ)*((a+1:ℕ):ℤ))=q^(-(m:ℤ)*(a:ℤ))*q^(-(m:ℤ)) := by
      rw [← zpow_add₀ (ne_of_gt hq)]
      congr 1
      push_cast
      ring
    have hmphase : (m:ℤ)-2*(m:ℤ)=-(m:ℤ) := by omega
    rw [hmphase,hphase,qfactorial_succ,qnum_eq_qInteger q hq hq1]
    have ha : (a:ℤ)+1=((a+1:ℕ):ℤ) := by omega
    rw [ha]
    ring

end AMSPhysical

#print axioms AMSPhysical.standardWeightBasis_E_power
#print axioms AMSPhysical.finiteTensor_E_power_last_coefficient
