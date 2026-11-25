import QuantumLatticeRoots
import QuantumIntegerRecurrence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

variable {K ι : Type*} [Field K] [DecidableEq ι]

/-- First adjacent-root quantum Serre relation in arbitrary rank. -/
theorem quantumLatticeMove_serre_left (q : K) (hq : q≠0) (hD : q-q⁻¹≠0)
    (i j k : ι) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    quantumLatticeMove q i j*quantumLatticeMove q i j*quantumLatticeMove q j k-
      (q+q⁻¹) • (quantumLatticeMove q i j*quantumLatticeMove q j k*quantumLatticeMove q i j)+
      quantumLatticeMove q j k*quantumLatticeMove q i j*quantumLatticeMove q i j=0 := by
  apply Finsupp.lhom_ext
  intro x a
  have hi₁ : x+latticeRoot i j+latticeRoot j k+latticeRoot i j=
      x+latticeRoot j k+latticeRoot i j+latticeRoot i j := by abel
  have hi₂ : x+latticeRoot i j+latticeRoot i j+latticeRoot j k=
      x+latticeRoot j k+latticeRoot i j+latticeRoot i j := by abel
  have hj₁ : x j+1+(-1)=x j := by ring
  have hj₂ : x j+(-1)+1=x j := by ring
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,quantumLatticeMove_single,
    LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul,LinearMap.zero_apply,Pi.add_apply,
    latticeRoot_target j k hjk,latticeRoot_source i j hij,
    latticeRoot_other i j k (Ne.symm hik) (Ne.symm hjk),add_zero,hj₁,hj₂,hi₁,hi₂,
    ← Finsupp.single_sub,← Finsupp.single_add,Finsupp.single_eq_zero]
  have hc := qInteger_second_order q hq hD (x j)
  simp only [sub_eq_add_neg] at hc
  linear_combination a*qInteger q (x j)*qInteger q (x k)*hc

/-- The other orientation of the adjacent-root Serre relation. -/
theorem quantumLatticeMove_serre_right (q : K) (hq : q≠0) (hD : q-q⁻¹≠0)
    (i j k : ι) (hjk : j≠k) (hik : i≠k) :
    quantumLatticeMove q j k*quantumLatticeMove q j k*quantumLatticeMove q i j-
      (q+q⁻¹) • (quantumLatticeMove q j k*quantumLatticeMove q i j*quantumLatticeMove q j k)+
      quantumLatticeMove q i j*quantumLatticeMove q j k*quantumLatticeMove q j k=0 := by
  apply Finsupp.lhom_ext
  intro x a
  have hi₁ : x+latticeRoot j k+latticeRoot i j+latticeRoot j k=
      x+latticeRoot i j+latticeRoot j k+latticeRoot j k := by abel
  have hi₂ : x+latticeRoot j k+latticeRoot j k+latticeRoot i j=
      x+latticeRoot i j+latticeRoot j k+latticeRoot j k := by abel
  have hj₁ : x j+1+1=x j+2 := by ring
  have hj₂ : (x j+1)-1=x j := by ring
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,quantumLatticeMove_single,
    LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul,LinearMap.zero_apply,Pi.add_apply,
    latticeRoot_target j k hjk,latticeRoot_source j k hjk,
    latticeRoot_other i j k (Ne.symm hik) (Ne.symm hjk),add_zero,hj₁,hi₁,hi₂,
    ← Finsupp.single_sub,← Finsupp.single_add,Finsupp.single_eq_zero]
  have hc := qInteger_second_order q hq hD (x j+1)
  rw [hj₁,hj₂] at hc
  linear_combination a*qInteger q (x k)*qInteger q (x k+(-1))*hc

end AMSPhysical

#print axioms AMSPhysical.quantumLatticeMove_serre_left
#print axioms AMSPhysical.quantumLatticeMove_serre_right
