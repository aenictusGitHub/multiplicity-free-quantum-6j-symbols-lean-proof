import QuantumOccupationShifts
import QuantumOccupationWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

/-- Exact square-sum change after adding a symmetric endpoint degree. -/
theorem occupationSquareSum_single_add (n : ℕ) (t : Fin (n+1) → ℤ) (k : Fin (n+1)) (a : ℤ) :
    occupationSquareSum (t+(Pi.single k a : Fin (n+1) → ℤ))=occupationSquareSum t+2*a*t k+a^2 := by
  classical
  have he (j : Fin (n+1)) : ((t+(Pi.single k a : Fin (n+1) → ℤ)) j)^2=(t j)^2+
      (if j=k then 2*a*t k+a^2 else 0) := by
    by_cases hj : j=k
    · subst j
      simp only [Pi.add_apply,Pi.single_eq_same,ite_true]
      ring
    · simp [Pi.single_apply,hj,Ne.symm hj]
  simp only [occupationSquareSum,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

theorem shiftedOccupation_energy (n r a : ℕ) (k : Fin (n+1)) (t : occupationWeights (Fin (n+1)) r) :
    occupationEnergy n (r+a) (shiftedOccupation n r a k t)=occupationEnergy n r t+(a:ℤ)*(t.val k-r) := by
  have he : occupationSquareSum (shiftedOccupation n r a k t).val-((r+a:ℕ):ℤ)^2=
      occupationSquareSum t.val-(r:ℤ)^2+2*((a:ℤ)*(t.val k-r)) := by
    change occupationSquareSum (t.val+(Pi.single k (a:ℤ) : Fin (n+1) → ℤ))-((r+a:ℕ):ℤ)^2=_
    rw [occupationSquareSum_single_add]
    push_cast
    ring
  unfold occupationEnergy
  omega

theorem shiftedOccupation_heightZ (n r a : ℕ) (k : Fin (n+1)) (t : occupationWeights (Fin (n+1)) r) :
    occupationHeightZ n (r+a) (shiftedOccupation n r a k t)=occupationHeightZ n r t+(k.val:ℤ)*a := by
  unfold occupationHeightZ shiftedOccupation
  rw [latticePairing_add_right]
  congr 1
  simp [latticePairing,Pi.single_apply,eq_comm,Finset.mul_sum]

theorem shiftedOccupation_factorials (q : ℝ) (n r a : ℕ) (k : Fin (n+1)) (t : occupationWeights (Fin (n+1)) r) :
    qfactorial q ((t.val k).toNat)*occupationFactorialProduct q n (r+a) (shiftedOccupation n r a k t)=
      qfactorial q ((t.val k).toNat+a)*occupationFactorialProduct q n r t := by
  classical
  have he (j : Fin (n+1)) :
      (if j=k then qfactorial q ((t.val k).toNat) else 1)*
        qfactorial q (((shiftedOccupation n r a k t).val j).toNat)=
      (if j=k then qfactorial q ((t.val k).toNat+a) else 1)*qfactorial q ((t.val j).toNat) := by
    by_cases hj : j=k
    · subst j
      have hn : ((shiftedOccupation n r a k t).val k).toNat=(t.val k).toNat+a := by
        have ht := t.property.1 k
        change ((t.val+(Pi.single k (a:ℤ) : Fin (n+1) → ℤ)) k).toNat=_
        simp only [Pi.add_apply,Pi.single_eq_same]
        omega
      rw [if_pos rfl,if_pos rfl,hn,mul_comm]
    · have hzero : (shiftedOccupation n r a k t).val j=t.val j := by
        simp [shiftedOccupation,Pi.single_apply,hj,Ne.symm hj]
      rw [if_neg hj,if_neg hj,hzero]
  have hp := Finset.prod_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun j _ => he j)
  simpa only [Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true] using hp

end AMSPhysical
#print axioms AMSPhysical.shiftedOccupation_factorials
