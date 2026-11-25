import QuantumTensorCoordinates
import QuantumProjectedTriangular

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

/-- The independently presented Casimir is a second-order difference operator in tensor weights. -/
theorem finiteTensor_Casimir_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) :
    finiteTensorCoefficient l m y z
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqCasimir q) p)=
    (q-q⁻¹)^2*(qInteger q ((l:ℤ)-y+1)*
        (qInteger q y*q^((m:ℤ)-2*z)*finiteTensorCoefficient l m y z p+
          qInteger q (z+1)*finiteTensorCoefficient l m (y-1) (z+1) p)+
      q^(-(l:ℤ)+2*y)*qInteger q ((m:ℤ)-z+1)*
        (qInteger q (y+1)*q^((m:ℤ)-2*(z-1))*finiteTensorCoefficient l m (y+1) (z-1) p+
          qInteger q z*finiteTensorCoefficient l m y z p))+
      q*(q^((l:ℤ)+(m:ℤ)-2*(y+z))*finiteTensorCoefficient l m y z p)+
      q⁻¹*(q^(-((l:ℤ)+(m:ℤ)-2*(y+z)))*finiteTensorCoefficient l m y z p) := by
  simp only [uqCasimir,map_add,map_smul,map_mul,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.mul_apply,smul_eq_mul]
  rw [finiteTensor_F_coefficient q hq hq1 l m y z,
    finiteTensor_E_coefficient q hq hq1 l m (y-1) z,
    finiteTensor_E_coefficient q hq hq1 l m y (z-1),
    finiteTensor_K_coefficient q hq hq1 l m y z,finiteTensor_Ki_coefficient q hq hq1 l m y z]
  simp only [sub_add_cancel]

/-- A lower support cutoff drops by at most one under the actual Casimir. -/
theorem finiteTensor_Casimir_support (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) (cut y z : ℤ)
    (hzero : ∀ a b,a<cut → finiteTensorCoefficient l m a b p=0) (hy : y+1<cut) :
    finiteTensorCoefficient l m y z
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqCasimir q) p)=0 := by
  rw [finiteTensor_Casimir_coefficient q hq hq1 l m y z p]
  rw [hzero y z (by omega),hzero (y-1) (z+1) (by omega),hzero (y+1) (z-1) hy]
  ring

theorem quantumLeftTreeHighest_Casimir_projected_below (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (y z : ℤ) (hy : y+1<(p.1.val:ℤ)) :
    finiteTensorCoefficient m n y z (firstTripleProjection l m n
      (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)))=0 := by
  rw [firstTripleProjection_Casimir]
  exact finiteTensor_Casimir_support q hq hq1 m n _ p.1.val y z
    (fun a b ha => quantumLeftTreeHighest_projected_below q hq hq1 l m n p a b ha) hy

end AMSPhysical

#print axioms AMSPhysical.finiteTensor_Casimir_coefficient
#print axioms AMSPhysical.quantumLeftTreeHighest_Casimir_projected_below
