import QuantumTypeAInverseWeights
import QuantumTensorSerre

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {K : Type*} [Field K]
local notation "U" => typeAAlgebraGenerator

def typeACoproductE (q : K) (n : ℕ) (i : Fin n) : UqTypeA q n ⊗[K] UqTypeA q n :=
  U q n i 0 ⊗ₜ[K] U q n i 2+(1:UqTypeA q n) ⊗ₜ[K] U q n i 0

def typeACoproductF (q : K) (n : ℕ) (i : Fin n) : UqTypeA q n ⊗[K] UqTypeA q n :=
  U q n i 1 ⊗ₜ[K] (1:UqTypeA q n)+U q n i 3 ⊗ₜ[K] U q n i 1

def typeACoproductK (q : K) (n : ℕ) (i : Fin n) : UqTypeA q n ⊗[K] UqTypeA q n :=
  U q n i 2 ⊗ₜ[K] U q n i 2

def typeACoproductKi (q : K) (n : ℕ) (i : Fin n) : UqTypeA q n ⊗[K] UqTypeA q n :=
  U q n i 3 ⊗ₜ[K] U q n i 3

theorem typeACoproduct_inverse (q : K) (n : ℕ) (i : Fin n) :
    typeACoproductK q n i*typeACoproductKi q n i=1 := by
  simp only [typeACoproductK,typeACoproductKi,Algebra.TensorProduct.tmul_mul_tmul,
    uqA_inverse,← Algebra.TensorProduct.one_def]

theorem typeACoproduct_inverse' (q : K) (n : ℕ) (i : Fin n) :
    typeACoproductKi q n i*typeACoproductK q n i=1 := by
  simp only [typeACoproductK,typeACoproductKi,Algebra.TensorProduct.tmul_mul_tmul,
    uqA_inverse',← Algebra.TensorProduct.one_def]

theorem typeACoproduct_torus (q : K) (n : ℕ) (i j : Fin n) :
    typeACoproductK q n i*typeACoproductK q n j=typeACoproductK q n j*typeACoproductK q n i := by
  simp only [typeACoproductK,Algebra.TensorProduct.tmul_mul_tmul]
  rw [uqA_torus q n i j]

theorem typeACoproduct_weightE (q : K) (n : ℕ) (i j : Fin n) :
    typeACoproductK q n i*typeACoproductE q n j=
      q^(typeACartan n i j) • (typeACoproductE q n j*typeACoproductK q n i) := by
  simp only [typeACoproductK,typeACoproductE,mul_add,add_mul,Algebra.TensorProduct.tmul_mul_tmul,
    mul_one,one_mul,uqA_weightE,TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_add]
  rw [uqA_torus q n i j]

theorem typeACoproduct_weightF (q : K) (n : ℕ) (i j : Fin n) :
    typeACoproductK q n i*typeACoproductF q n j=
      q^(-typeACartan n i j) • (typeACoproductF q n j*typeACoproductK q n i) := by
  simp only [typeACoproductK,typeACoproductF,mul_add,add_mul,Algebra.TensorProduct.tmul_mul_tmul,
    mul_one,one_mul,uqA_weightF,TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_add]
  rw [uqA_torus_inverse_right q n i j]

theorem typeACoproduct_cross_commutes (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    (U q n i 0 ⊗ₜ[K] U q n i 2)*(U q n j 3 ⊗ₜ[K] U q n j 1)=
      (U q n j 3 ⊗ₜ[K] U q n j 1)*(U q n i 0 ⊗ₜ[K] U q n i 2) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul,uqA_E_Kinv,uqA_weightF,
    ← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [typeACartan_symmetric n j i,mul_comm (q^(-typeACartan n i j)) (q^(typeACartan n i j)),
    zpow_opposite_product q hq,one_smul]

theorem typeACoproduct_commutator_expand (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    typeACoproductE q n i*typeACoproductF q n j-typeACoproductF q n j*typeACoproductE q n i=
      (U q n i 0*U q n j 1-U q n j 1*U q n i 0) ⊗ₜ[K] U q n i 2+
      U q n j 3 ⊗ₜ[K] (U q n i 0*U q n j 1-U q n j 1*U q n i 0) := by
  have hc := typeACoproduct_cross_commutes q hq n i j
  have hc' : ((1:UqTypeA q n) ⊗ₜ[K] U q n i 0)*(U q n j 1 ⊗ₜ[K] (1:UqTypeA q n))=
      (U q n j 1 ⊗ₜ[K] (1:UqTypeA q n))*((1:UqTypeA q n) ⊗ₜ[K] U q n i 0) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]
  calc
    _ = ((U q n i 0 ⊗ₜ[K] U q n i 2)*(U q n j 1 ⊗ₜ[K] (1:UqTypeA q n))-
        (U q n j 1 ⊗ₜ[K] (1:UqTypeA q n))*(U q n i 0 ⊗ₜ[K] U q n i 2))+
      (((1:UqTypeA q n) ⊗ₜ[K] U q n i 0)*(U q n j 3 ⊗ₜ[K] U q n j 1)-
        (U q n j 3 ⊗ₜ[K] U q n j 1)*((1:UqTypeA q n) ⊗ₜ[K] U q n i 0)) := by
      unfold typeACoproductE typeACoproductF
      simp only [mul_add,add_mul]
      rw [hc,hc']
      abel
    _ = _ := by simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,
      TensorProduct.sub_tmul,TensorProduct.tmul_sub]

theorem typeACoproduct_commutator (q : K) (hq : q≠0) (n : ℕ) (i : Fin n) :
    typeACoproductE q n i*typeACoproductF q n i-typeACoproductF q n i*typeACoproductE q n i=
      (q-q⁻¹)⁻¹ • (typeACoproductK q n i-typeACoproductKi q n i) := by
  rw [typeACoproduct_commutator_expand q hq,uqA_commutator]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,TensorProduct.sub_tmul,
    TensorProduct.tmul_sub,smul_add,smul_sub,typeACoproductK,typeACoproductKi]
  abel

theorem typeACoproduct_differentEF (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) (hij : i≠j) :
    typeACoproductE q n i*typeACoproductF q n j=typeACoproductF q n j*typeACoproductE q n i := by
  have hh := typeACoproduct_commutator_expand q hq n i j
  rw [uqA_differentEF q n i j hij,sub_self,TensorProduct.zero_tmul,TensorProduct.tmul_zero,zero_add] at hh
  exact sub_eq_zero.mp hh

end AMSPhysical
#print axioms AMSPhysical.typeACoproduct_commutator
