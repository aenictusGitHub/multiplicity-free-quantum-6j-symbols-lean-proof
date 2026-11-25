import QuantumOccupationReflection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

theorem quantumOccupationReflection_comp_self (n L : ℕ) :
    (quantumOccupationReflection n L).toLinearMap.comp (quantumOccupationReflection n L).toLinearMap=LinearMap.id := by
  apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
  intro x
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumOccupationReflection_basis,
    LinearMap.id_apply]
  rw [occupationReflection_involutive n L x]

theorem quantumOccupationReflection_involutive (n L : ℕ) : Function.Involutive (quantumOccupationReflection n L) := by
  intro v
  exact DFunLike.congr_fun (quantumOccupationReflection_comp_self n L) v

theorem quantumOccupationReflection_twice (n L : ℕ) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    quantumOccupationReflection n L (quantumOccupationReflection n L v)=v :=
  quantumOccupationReflection_involutive n L v

end AMSPhysical
#print axioms AMSPhysical.quantumOccupationReflection_involutive
