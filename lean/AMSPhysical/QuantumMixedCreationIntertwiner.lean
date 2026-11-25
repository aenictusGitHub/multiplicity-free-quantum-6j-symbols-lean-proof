import QuantumMixedFiniteCreation
import QuantumMixedCoefficientLowering
import QuantumMixedCoefficientCartan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFiniteCreation_intertwines_F (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m : ℕ) (i : Fin n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedFiniteCreation q n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 1) v)=
      typeAMixedTensor q hq hD n (l+1) (m+1) (typeAAlgebraGenerator q n i 1) (mixedFiniteCreation q n l m v) := by
  apply occupationTensorCoefficients_injective n (l+1) (m+1)
  rw [occupationTensorCoefficients_creation,occupationTensorCoefficients_mixed_F,
    occupationTensorCoefficients_mixed_F,occupationTensorCoefficients_creation]
  exact DFunLike.congr_fun (pairLatticeCreation_commutes_lowering q hq hD n i) _

theorem mixedFiniteCreation_intertwines_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m : ℕ) (i : Fin n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedFiniteCreation q n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) v)=
      typeAMixedTensor q hq hD n (l+1) (m+1) (typeAAlgebraGenerator q n i 2) (mixedFiniteCreation q n l m v) := by
  apply occupationTensorCoefficients_injective n (l+1) (m+1)
  rw [occupationTensorCoefficients_creation,occupationTensorCoefficients_mixed_K,
    occupationTensorCoefficients_mixed_K,occupationTensorCoefficients_creation]
  exact DFunLike.congr_fun (pairLatticeCreation_commutes_cartan q n i 1) _

theorem mixedFiniteCreation_intertwines_Ki (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m : ℕ) (i : Fin n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedFiniteCreation q n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 3) v)=
      typeAMixedTensor q hq hD n (l+1) (m+1) (typeAAlgebraGenerator q n i 3) (mixedFiniteCreation q n l m v) := by
  apply occupationTensorCoefficients_injective n (l+1) (m+1)
  rw [occupationTensorCoefficients_creation,occupationTensorCoefficients_mixed_Ki,
    occupationTensorCoefficients_mixed_Ki,occupationTensorCoefficients_creation]
  exact DFunLike.congr_fun (pairLatticeCreation_commutes_cartan q n i (-1)) _

/-- The explicit finite creation operator intertwines the ENTIRE independently
presented quantum group in every rank and pair of symmetric degrees. -/
theorem mixedFiniteCreation_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m : ℕ) (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedFiniteCreation q n l m (typeAMixedTensor q hq hD n l m z v)=
      typeAMixedTensor q hq hD n (l+1) (m+1) z (mixedFiniteCreation q n l m v) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  apply typeA_intertwiner_of_generators (V:=V) (W:=W) q n _ _ _ _ z v
  intro i t x
  fin_cases t
  · exact mixedFiniteCreation_intertwines_E q hq hD n l m i x
  · exact mixedFiniteCreation_intertwines_F q hq hD n l m i x
  · exact mixedFiniteCreation_intertwines_K q hq hD n l m i x
  · exact mixedFiniteCreation_intertwines_Ki q hq hD n l m i x

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreation_intertwines
