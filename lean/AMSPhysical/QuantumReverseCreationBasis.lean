import QuantumReverseMixedCreation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem reverseMixedFiniteCreation_basis (q : ℝ) (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    reverseMixedFiniteCreation q n l m
        (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      ∑ j : Fin (n+1),mixedCreationCoefficient q n j.rev
        ((occupationReflection n l x).val,(occupationReflection n m y).val) •
          (quantumOccupationBasis (K:=ℝ) (l+1) (shiftedOccupation n l 1 j x) ⊗ₜ[ℝ]
            quantumOccupationBasis (K:=ℝ) (m+1) (shiftedOccupation n m 1 j y)) := by
  unfold reverseMixedFiniteCreation
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,mixedReflection_inverse_basis,mixedFiniteCreation_basis,
    map_sum,map_smul,mixedReflection_basis,occupationReflection_unit_shift,occupationReflection_involutive]
  rw [occupationReflection_involutive n l x,occupationReflection_involutive n m y]
  have hs:=Equiv.sum_comp Fin.revPerm (fun j : Fin (n+1) =>mixedCreationCoefficient q n j.rev
    ((occupationReflection n l x).val,(occupationReflection n m y).val) •
      (quantumOccupationBasis (K:=ℝ) (l+1) (shiftedOccupation n l 1 j x) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) (m+1) (shiftedOccupation n m 1 j y)))
  simpa only [Fin.revPerm_apply,Fin.rev_rev,occupationReflection_involutive] using hs

end AMSPhysical
