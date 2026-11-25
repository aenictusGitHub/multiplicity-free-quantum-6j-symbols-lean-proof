import ClassicalUniversalNormalization
import ClassicalKZReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

theorem classicalUniversalI_XY (h : ℕ) (r : Fin 4 → ℕ)
    (p : fixedGLInvariants (K:=ℂ) (2+h) r) :
    classicalUniversalI h r (glXYEnd h r p)=typeIXYEnd h r (classicalUniversalI h r p) := by
  change determinantUniversalScale h • classicalRankReductionI h r (glXYEnd h r p)=
    typeIXYEnd h r (determinantUniversalScale h • classicalRankReductionI h r p)
  rw [rankReductionI_XY,map_smul]

theorem classicalUniversalI_ZY (h : ℕ) (r : Fin 4 → ℕ)
    (p : fixedGLInvariants (K:=ℂ) (2+h) r) :
    classicalUniversalI h r (glZYEnd h r p)=typeIZYEnd h r (classicalUniversalI h r p) := by
  change determinantUniversalScale h • classicalRankReductionI h r (glZYEnd h r p)=
    typeIZYEnd h r (determinantUniversalScale h • classicalRankReductionI h r p)
  rw [rankReductionI_ZY,map_smul]

theorem classicalUniversalII_XX (h : ℕ) (r : Fin 4 → ℕ)
    (p : fixedGLInvariants (K:=ℂ) (2+h) r) :
    classicalUniversalII h r (glXXEnd h r p)=typeIIXXEnd h r (classicalUniversalII h r p) := by
  change determinantUniversalScale h • classicalRankReductionII h r (glXXEnd h r p)=
    typeIIXXEnd h r (determinantUniversalScale h • classicalRankReductionII h r p)
  rw [rankReductionII_XX,map_smul]

theorem classicalUniversalII_ZY (h : ℕ) (r : Fin 4 → ℕ)
    (p : fixedGLInvariants (K:=ℂ) (2+h) r) :
    classicalUniversalII h r (glZYEnd h r p)=typeIIZYEnd h r (classicalUniversalII h r p) := by
  change determinantUniversalScale h • classicalRankReductionII h r (glZYEnd h r p)=
    typeIIZYEnd h r (determinantUniversalScale h • classicalRankReductionII h r p)
  rw [rankReductionII_ZY,map_smul]

theorem orthonormalMatrix_mapped_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E) (e : E ≃ₗᵢ[ℂ] F)
    (A : Module.End ℂ E) (B : Module.End ℂ F) (hAB : ∀ x,B (e x)=e (A x)) :
    orthonormalMatrix n (v.map e) B=orthonormalMatrix n v A := by
  ext i j
  simp only [orthonormalMatrix,CStarMatrix.ofMatrix_apply,LinearMap.toMatrix_apply]
  change ((v.map e).toBasis.repr (B ((v.map e) j))) i=(v.toBasis.repr (A (v j))) i
  rw [OrthonormalBasis.map_apply,hAB]
  change (v.repr (e.symm (e (A (v j))))) i=(v.repr (A (v j))) i
  rw [e.symm_apply_apply]

end AMSPhysical
#print axioms AMSPhysical.classicalUniversalI_XY
#print axioms AMSPhysical.orthonormalMatrix_mapped_isometry
