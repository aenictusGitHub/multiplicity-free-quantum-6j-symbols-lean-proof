import QuantumSerreSum
import Mathlib.RingTheory.TensorProduct.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

theorem serre_tensor_right (q : K) (X Y : A) (H J : B) (hHJ : H*J=J*H) :
    serrePolynomial q (X ⊗ₜ[K] H) (Y ⊗ₜ[K] J)=serrePolynomial q X Y ⊗ₜ[K] (H*H*J) := by
  have h₁ : H*J*H=H*H*J := by rw [mul_assoc,← hHJ];noncomm_ring
  have h₂ : J*H*H=H*H*J := by rw [← hHJ];exact h₁
  simp only [serrePolynomial,Algebra.TensorProduct.tmul_mul_tmul,h₁,h₂,
    TensorProduct.sub_tmul,TensorProduct.add_tmul,TensorProduct.smul_tmul']

theorem serre_tensor_left (q : K) (H J : A) (X Y : B) (hHJ : H*J=J*H) :
    serrePolynomial q (H ⊗ₜ[K] X) (J ⊗ₜ[K] Y)=(H*H*J) ⊗ₜ[K] serrePolynomial q X Y := by
  have h₁ : H*J*H=H*H*J := by rw [mul_assoc,← hHJ];noncomm_ring
  have h₂ : J*H*H=H*H*J := by rw [← hHJ];exact h₁
  simp only [serrePolynomial,Algebra.TensorProduct.tmul_mul_tmul,h₁,h₂,
    TensorProduct.tmul_sub,TensorProduct.tmul_add,TensorProduct.tmul_smul]

theorem serre_tensor_one_right (q : K) (X Y : A) :
    serrePolynomial q (X ⊗ₜ[K] (1:B)) (Y ⊗ₜ[K] (1:B))=serrePolynomial q X Y ⊗ₜ[K] (1:B) := by
  simpa only [one_mul] using serre_tensor_right q X Y (1:B) 1 rfl

theorem serre_tensor_one_left (q : K) (X Y : B) :
    serrePolynomial q ((1:A) ⊗ₜ[K] X) ((1:A) ⊗ₜ[K] Y)=(1:A) ⊗ₜ[K] serrePolynomial q X Y := by
  simpa only [one_mul] using serre_tensor_left q (1:A) 1 X Y rfl

theorem serrePolynomial_inverse_parameter (q : K) (X Y : A) :
    serrePolynomial q⁻¹ X Y=serrePolynomial q X Y := by
  simp only [serrePolynomial,inv_inv,add_comm q⁻¹ q]

end AMSPhysical

#print axioms AMSPhysical.serre_tensor_right
