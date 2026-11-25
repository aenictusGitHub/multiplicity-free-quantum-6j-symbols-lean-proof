import QuantumTypeARelations

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]
local notation "U" => typeAAlgebraGenerator

theorem zpow_opposite_product (q : K) (hq : q≠0) (a : ℤ) : q^a*q^(-a)=1 := by
  rw [← zpow_add₀ hq,add_neg_cancel,zpow_zero]

theorem uqA_E_K (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    U q n j 0*U q n i 2=q^(-typeACartan n i j) • (U q n i 2*U q n j 0) := by
  rw [uqA_weightE,smul_smul]
  have hp : q^(-typeACartan n i j)*q^(typeACartan n i j)=1 := by
    rw [← zpow_add₀ hq,neg_add_cancel,zpow_zero]
  rw [hp,one_smul]

theorem uqA_F_K (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    U q n j 1*U q n i 2=q^(typeACartan n i j) • (U q n i 2*U q n j 1) := by
  rw [uqA_weightF,smul_smul,zpow_opposite_product q hq,one_smul]

theorem uqA_Kinv_E (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    U q n i 3*U q n j 0=q^(-typeACartan n i j) • (U q n j 0*U q n i 3) := by
  rw [uqA_E_Kinv,smul_smul]
  have hp : q^(-typeACartan n i j)*q^(typeACartan n i j)=1 := by
    rw [← zpow_add₀ hq,neg_add_cancel,zpow_zero]
  rw [hp,one_smul]

theorem uqA_Kinv_F (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    U q n i 3*U q n j 1=q^(typeACartan n i j) • (U q n j 1*U q n i 3) := by
  rw [uqA_F_Kinv,smul_smul,zpow_opposite_product q hq,one_smul]

end AMSPhysical

#print axioms AMSPhysical.uqA_Kinv_E
