import QuantumTypeACoproductBasic

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

theorem typeACoproduct_E_cross (q : K) (n : ℕ) (i j : Fin n) :
    (U q n i 0 ⊗ₜ[K] U q n i 2)*((1:UqTypeA q n) ⊗ₜ[K] U q n j 0)=
      q^(typeACartan n i j) • (((1:UqTypeA q n) ⊗ₜ[K] U q n j 0)*(U q n i 0 ⊗ₜ[K] U q n i 2)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,uqA_weightE,TensorProduct.tmul_smul]

theorem typeACoproduct_F_cross (q : K) (n : ℕ) (i j : Fin n) :
    (U q n i 1 ⊗ₜ[K] (1:UqTypeA q n))*(U q n j 3 ⊗ₜ[K] U q n j 1)=
      q^(-typeACartan n j i) • ((U q n j 3 ⊗ₜ[K] U q n j 1)*(U q n i 1 ⊗ₜ[K] (1:UqTypeA q n))) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,uqA_F_Kinv,TensorProduct.smul_tmul']

theorem typeACoproduct_serreE_of (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n)
    (ha : typeACartan n i j= -1) (hs : serrePolynomial q (U q n i 0) (U q n j 0)=0) :
    serrePolynomial q (typeACoproductE q n i) (typeACoproductE q n j)=0 := by
  have hb : typeACartan n j i= -1 := by rw [typeACartan_symmetric,ha]
  apply serrePolynomial_coproduct_sum q hq
  · simpa only [typeACartan_self,zpow_ofNat] using typeACoproduct_E_cross q n i i
  · simpa only [ha,zpow_neg_one] using typeACoproduct_E_cross q n i j
  · simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,uqA_E_K q hq,hb,
      neg_neg,zpow_one,TensorProduct.tmul_smul]
  · rw [serre_tensor_right q _ _ _ _ (uqA_torus q n i j),hs,TensorProduct.zero_tmul]
  · rw [serre_tensor_one_left,hs,TensorProduct.tmul_zero]

theorem typeACoproduct_serreF_of (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n)
    (ha : typeACartan n i j= -1) (hs : serrePolynomial q (U q n i 1) (U q n j 1)=0) :
    serrePolynomial q (typeACoproductF q n i) (typeACoproductF q n j)=0 := by
  have hb : typeACartan n j i= -1 := by rw [typeACartan_symmetric,ha]
  rw [← serrePolynomial_inverse_parameter]
  apply serrePolynomial_coproduct_sum q⁻¹ (inv_ne_zero hq)
  · simpa only [typeACartan_self,zpow_neg,zpow_ofNat,inv_pow] using typeACoproduct_F_cross q n i i
  · simpa only [hb,neg_neg,zpow_one,inv_inv] using typeACoproduct_F_cross q n i j
  · simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,uqA_Kinv_F q hq,ha,
      zpow_neg_one,TensorProduct.smul_tmul']
  · rw [serre_tensor_one_right,serrePolynomial_inverse_parameter,hs,TensorProduct.zero_tmul]
  · rw [serre_tensor_left q⁻¹ _ _ _ _ (uqA_torus_inverses q n i j),
      serrePolynomial_inverse_parameter,hs,TensorProduct.tmul_zero]

theorem typeACoproduct_serreELeft (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (typeACoproductE q n i) (typeACoproductE q n j)=0 :=
  typeACoproduct_serreE_of q hq n i j (typeACartan_adjacent n i j hij) (uqA_serreELeft q n i j hij)

theorem typeACoproduct_serreERight (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (typeACoproductE q n j) (typeACoproductE q n i)=0 :=
  typeACoproduct_serreE_of q hq n j i (by rw [typeACartan_symmetric];exact typeACartan_adjacent n i j hij)
    (uqA_serreERight q n i j hij)

theorem typeACoproduct_serreFLeft (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (typeACoproductF q n i) (typeACoproductF q n j)=0 :=
  typeACoproduct_serreF_of q hq n i j (typeACartan_adjacent n i j hij) (uqA_serreFLeft q n i j hij)

theorem typeACoproduct_serreFRight (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (typeACoproductF q n j) (typeACoproductF q n i)=0 :=
  typeACoproduct_serreF_of q hq n j i (by rw [typeACartan_symmetric];exact typeACartan_adjacent n i j hij)
    (uqA_serreFRight q n i j hij)

end AMSPhysical
#print axioms AMSPhysical.typeACoproduct_serreFRight
