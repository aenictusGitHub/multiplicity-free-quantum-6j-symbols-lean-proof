import QuantumTypeACoproductSerre

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {K : Type*} [Field K]
local notation "U" => typeAAlgebraGenerator

theorem commute_four_sum {A : Type*} [Ring A] (X Z Y W : A)
    (hXY : X*Y=Y*X) (hXW : X*W=W*X) (hZY : Z*Y=Y*Z) (hZW : Z*W=W*Z) :
    (X+Z)*(Y+W)=(Y+W)*(X+Z) := by
  simp only [mul_add,add_mul]
  rw [hXY,hXW,hZY,hZW]
  abel

theorem typeACoproduct_distantE (q : K) (n : ℕ) (i j : Fin n)
    (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    typeACoproductE q n i*typeACoproductE q n j=typeACoproductE q n j*typeACoproductE q n i := by
  have ha := typeACartan_distant n i j hd
  have hb : typeACartan n j i=0 := by rw [typeACartan_symmetric,ha]
  unfold typeACoproductE
  apply commute_four_sum (A:=UqTypeA q n ⊗[K] UqTypeA q n)
  · simp only [Algebra.TensorProduct.tmul_mul_tmul]
    rw [uqA_distantE q n i j hd,uqA_torus q n i j]
  · simpa only [ha,zpow_zero,one_smul] using typeACoproduct_E_cross q n i j
  · simpa only [hb,zpow_zero,one_smul] using (typeACoproduct_E_cross q n j i).symm
  · simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
    rw [uqA_distantE q n i j hd]

theorem typeACoproduct_distantF (q : K) (n : ℕ) (i j : Fin n)
    (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    typeACoproductF q n i*typeACoproductF q n j=typeACoproductF q n j*typeACoproductF q n i := by
  have ha := typeACartan_distant n i j hd
  have hb : typeACartan n j i=0 := by rw [typeACartan_symmetric,ha]
  unfold typeACoproductF
  apply commute_four_sum (A:=UqTypeA q n ⊗[K] UqTypeA q n)
  · simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one]
    rw [uqA_distantF q n i j hd]
  · simpa only [hb,neg_zero,zpow_zero,one_smul] using typeACoproduct_F_cross q n i j
  · simpa only [ha,neg_zero,zpow_zero,one_smul] using (typeACoproduct_F_cross q n j i).symm
  · simp only [Algebra.TensorProduct.tmul_mul_tmul]
    rw [uqA_torus_inverses q n i j,uqA_distantF q n i j hd]

end AMSPhysical
#print axioms AMSPhysical.typeACoproduct_distantF
