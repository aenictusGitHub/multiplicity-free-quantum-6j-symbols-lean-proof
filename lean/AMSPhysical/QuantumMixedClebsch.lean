import QuantumMixedChannelRepresentation
import QuantumMixedNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The actual normalized inclusion of a constructed mixed channel. -/
def mixedClebschMap (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    mixedChannelSubmodule q hq hD n r a b →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) :=
  (Real.sqrt (mixedCouplingNormClosed q n a b r))⁻¹ • (mixedChannelSubmodule q hq hD n r a b).subtype

def mixedChannelBilin (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    mixedChannelSubmodule q hq hD n r a b →ₗ[ℝ] mixedChannelSubmodule q hq hD n r a b →ₗ[ℝ] ℝ :=
  (mixedCouplingNormClosed q n a b r)⁻¹ •
    LinearMap.BilinForm.restrict (mixedTensorBilin q n (r+a) (r+b)) (mixedChannelSubmodule q hq hD n r a b)

/-- The constructed coupling map intertwines EVERY algebra element. -/
theorem mixedClebschMap_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ)
    (z : UqTypeA q n) (v : mixedChannelSubmodule q hq hD n r a b) :
    mixedClebschMap q hq hD n r a b (mixedChannelRepresentation q hq hD n r a b z v)=
      typeAMixedTensor q hq hD n (r+a) (r+b) z (mixedClebschMap q hq hD n r a b v) := by
  unfold mixedClebschMap
  simp only [LinearMap.smul_apply,Submodule.subtype_apply,map_smul]
  rfl

theorem mixedClebschMap_highest (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    mixedClebschMap q hq hD n r a b (mixedChannelHighest q hq hD n r a b)=
      normalizedMixedHighestVector q n r a b := rfl

/-- Actual isometry of the normalized higher-rank mixed Clebsch map, with
both source and target metrics explicitly constructed. -/
theorem mixedClebschMap_isometry (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0) (n r a b : ℕ)
    (v w : mixedChannelSubmodule q (ne_of_gt hq) hD n r a b) :
    mixedTensorBilin q n (r+a) (r+b) (mixedClebschMap q (ne_of_gt hq) hD n r a b v)
      (mixedClebschMap q (ne_of_gt hq) hD n r a b w)=
      mixedChannelBilin q (ne_of_gt hq) hD n r a b v w := by
  unfold mixedClebschMap mixedChannelBilin
  simp only [LinearMap.smul_apply,Submodule.subtype_apply,map_smul,Pi.smul_apply,smul_eq_mul,
    LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply]
  have hp := mixedCouplingNormClosed_pos q hq n a b r
  have hs := Real.sq_sqrt hp.le
  have hn := ne_of_gt hp
  have hs0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hn,hs0]
  rw [hs]
  ring

end AMSPhysical
#print axioms AMSPhysical.mixedClebschMap_intertwines
#print axioms AMSPhysical.mixedClebschMap_isometry
