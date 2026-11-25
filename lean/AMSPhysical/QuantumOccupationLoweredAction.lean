import QuantumOccupationLowering

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

theorem typeAFiniteGenerator_F_lowered (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.castSucc) :
    typeAFiniteGenerator q hq hD n L i 1 (quantumOccupationBasis (K:=K) L x)=
      qInteger q (x.val i.castSucc) • quantumOccupationBasis (K:=K) L (loweredOccupation n L x i hi) := by
  have h := typeAFiniteGenerator_F_reversed q hq hD n L (loweredOccupation n L x i hi) i
    (loweredOccupation_source_positive n L x i hi)
  rw [raised_loweredOccupation] at h
  have he : (loweredOccupation n L x i hi).val i.castSucc+1=x.val i.castSucc := by
    change (x.val+latticeRoot i.succ i.castSucc) i.castSucc+1=_
    rw [Pi.add_apply,latticeRoot_source _ _ (Ne.symm (typeA_root_endpoints n i))]
    ring
  rw [he] at h
  exact h

end AMSPhysical
