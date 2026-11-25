import MatrixPolar
import KZCentralShift
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped ComplexOrder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

def orthonormalMatrix (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E) (T : Module.End ℂ E) :
    CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (LinearMap.toMatrix v.toBasis v.toBasis T)

theorem orthonormalMatrix_selfadjoint (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E)
    (T : Module.End ℂ E) (hT : T.IsSymmetric) : IsSelfAdjoint (orthonormalMatrix n v T) := by
  have hh := (LinearMap.isSymmetric_iff_isSelfAdjoint T).mp hT
  change star ((LinearMap.toMatrixOrthonormal v) T)=(LinearMap.toMatrixOrthonormal v) T
  rw [← map_star,hh.star_eq]

theorem represented_equiv_isUnit (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E)
    (w : OrthonormalBasis (Fin n) ℂ F) (f : E ≃ₗ[ℂ] F) :
    IsUnit (CStarMatrix.ofMatrix (LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap)) := by
  let A : CStarMatrix (Fin n) (Fin n) ℂ :=
    CStarMatrix.ofMatrix (LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap)
  let B : CStarMatrix (Fin n) (Fin n) ℂ :=
    CStarMatrix.ofMatrix (LinearMap.toMatrix w.toBasis v.toBasis f.symm.toLinearMap)
  have hab : A*B=1 := by
    change LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap*
      LinearMap.toMatrix w.toBasis v.toBasis f.symm.toLinearMap=1
    rw [← LinearMap.toMatrix_comp]
    have hf : f.toLinearMap.comp f.symm.toLinearMap=LinearMap.id := by ext x; simp
    rw [hf,LinearMap.toMatrix_id]
  have hba : B*A=1 := by
    change LinearMap.toMatrix w.toBasis v.toBasis f.symm.toLinearMap*
      LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap=1
    rw [← LinearMap.toMatrix_comp]
    have hf : f.symm.toLinearMap.comp f.toLinearMap=LinearMap.id := by ext x; simp
    rw [hf,LinearMap.toMatrix_id]
  exact ⟨⟨A,B,hab,hba⟩,rfl⟩

theorem represented_intertwining (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E)
    (w : OrthonormalBasis (Fin n) ℂ F) (f : E ≃ₗ[ℂ] F)
    (a : Module.End ℂ E) (b : Module.End ℂ F) (h : ∀ x,b (f x)=f (a x)) :
    orthonormalMatrix n w b*CStarMatrix.ofMatrix (LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap)=
      CStarMatrix.ofMatrix (LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap)*orthonormalMatrix n v a := by
  change LinearMap.toMatrix w.toBasis w.toBasis b*LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap=
    LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap*LinearMap.toMatrix v.toBasis v.toBasis a
  rw [← LinearMap.toMatrix_comp,← LinearMap.toMatrix_comp]
  congr 1
  ext x
  exact h x

/-- Polar unitarization applied to genuine finite Hilbert-space operators in independently
chosen orthonormal bases. No matrix selfadjointness or invertibility is assumed. -/
theorem finiteHilbert_simultaneous_unitary (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E)
    (w : OrthonormalBasis (Fin n) ℂ F) (f : E ≃ₗ[ℂ] F)
    (a₁ a₂ : Module.End ℂ E) (b₁ b₂ : Module.End ℂ F)
    (ha₁ : a₁.IsSymmetric) (ha₂ : a₂.IsSymmetric) (hb₁ : b₁.IsSymmetric) (hb₂ : b₂.IsSymmetric)
    (h₁ : ∀ x,b₁ (f x)=f (a₁ x)) (h₂ : ∀ x,b₂ (f x)=f (a₂ x)) :
    ∃ S : unitary (CStarMatrix (Fin n) (Fin n) ℂ),
      orthonormalMatrix n w b₁*(S:CStarMatrix (Fin n) (Fin n) ℂ)=
        (S:CStarMatrix (Fin n) (Fin n) ℂ)*orthonormalMatrix n v a₁ ∧
      orthonormalMatrix n w b₂*(S:CStarMatrix (Fin n) (Fin n) ℂ)=
        (S:CStarMatrix (Fin n) (Fin n) ℂ)*orthonormalMatrix n v a₂ := by
  obtain ⟨s,hs,h₁s,h₂s⟩ := matrix_simultaneous_unitary n
    (orthonormalMatrix n v a₁) (orthonormalMatrix n v a₂)
    (orthonormalMatrix n w b₁) (orthonormalMatrix n w b₂)
    (CStarMatrix.ofMatrix (LinearMap.toMatrix v.toBasis w.toBasis f.toLinearMap))
    (represented_equiv_isUnit n v w f)
    (orthonormalMatrix_selfadjoint n v a₁ ha₁) (orthonormalMatrix_selfadjoint n v a₂ ha₂)
    (orthonormalMatrix_selfadjoint n w b₁ hb₁) (orthonormalMatrix_selfadjoint n w b₂ hb₂)
    (represented_intertwining n v w f a₁ b₁ h₁) (represented_intertwining n v w f a₂ b₂ h₂)
  exact ⟨⟨s,hs⟩,h₁s,h₂s⟩

end AMSPhysical

#print axioms AMSPhysical.finiteHilbert_simultaneous_unitary
