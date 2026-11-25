import QuantumTensorCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem finiteWeightCoefficient_outside (L : ℕ) (p : RealQuantumSpace L) (z : ℤ)
    (hz : z<0 ∨ (L:ℤ)<z) : p.val z=0 := by
  by_contra hn
  have hs : (p.val.support : Set ℤ)⊆Set.Icc 0 (L:ℤ) := p.property
  have hi := hs (Finsupp.mem_support_iff.mpr hn)
  rcases hi with ⟨hi0,hiL⟩
  rcases hz with hz | hz <;> omega

theorem finiteTensorCoefficient_outside_right (l m : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) (hz : z<0 ∨ (m:ℤ)<z) :
    finiteTensorCoefficient l m y z p=0 := by
  induction p using TensorProduct.induction_on with
  | zero => exact (finiteTensorCoefficient l m y z).map_zero
  | tmul a b => rw [finiteTensorCoefficient_tmul,finiteWeightCoefficient_outside m b z hz,mul_zero]
  | add a b ha hb => rw [map_add,ha,hb,add_zero]

/-- At the last weight of the second factor, the true E-intertwining equation has only one term. -/
theorem standardClebschCoefficient_last_E_step (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r)) (y : ℤ) :
    qInteger q ((k.val+1:ℕ):ℤ)*standardClebschCoefficient q hq hq1 l m r k.castSucc y m=
      qInteger q (y+1)*q^(-(m:ℤ))*standardClebschCoefficient q hq hq1 l m r k.succ (y+1) m := by
  have hT := unitaryQuantumClebschMap_intertwines q hq hq1 l m r (uqGenerator q 0)
    (standardWeightBasis (coupledLabel l m r) k.succ)
  have hg : finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (coupledLabel l m r) (uqGenerator q 0)=finiteQuantumE q (coupledLabel l m r) :=
    finiteQuantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (coupledLabel l m r) 0
  rw [hg,standardWeightBasis_E_succ,map_smul] at hT
  have he := congrArg (finiteTensorCoefficient l m y (m:ℤ)) hT
  rw [finiteTensor_E_coefficient q hq hq1 l m y m,
    finiteTensorCoefficient_outside_right l m y ((m:ℤ)+1) _ (Or.inr (by omega)),mul_zero,add_zero,
    map_smul,smul_eq_mul] at he
  have hphase : (m:ℤ)-2*(m:ℤ)=-(m:ℤ) := by omega
  rw [hphase] at he
  exact he.symm

end AMSPhysical

#print axioms AMSPhysical.standardClebschCoefficient_last_E_step
