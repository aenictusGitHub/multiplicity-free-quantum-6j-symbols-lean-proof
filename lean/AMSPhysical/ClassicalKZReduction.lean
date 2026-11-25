import FixedFockSpaces
import KZIntertwining

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped ComplexOrder

attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

def hilbertKZConnection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E)
    (A B : Module.End ℂ E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) (t : ℝ) :
    unitary (CStarMatrix (Fin n) (Fin n) ℂ) :=
  kzConnection n (imaginaryResidue n t (orthonormalMatrix n v A))
    (imaginaryResidue n t (orthonormalMatrix n v B))
    (imaginaryResidue_skew n t _ (orthonormalMatrix_selfadjoint n v A hA))
    (imaginaryResidue_skew n t _ (orthonormalMatrix_selfadjoint n v B hB))

/-- Fully constructed classical invariant-space Type-I KZ rank reduction. This is
an equality of canonical connection operators, not yet of physical quantum 6j symbols. -/
theorem classicalTypeI_KZ (h : ℕ) (r : Fin 4 → ℕ) :
    ∃ n : ℕ,∃ v : OrthonormalBasis (Fin n) ℂ (fixedGLInvariants (K:=ℂ) (2+h) r),
      ∃ w : OrthonormalBasis (Fin n) ℂ (fixedRelativeI (K:=ℂ) h r),
        ∃ S : unitary (CStarMatrix (Fin n) (Fin n) ℂ),∀ t : ℝ,
          (hilbertKZConnection n w (typeIXYEnd h r) (typeIZYEnd h r)
            (typeIXYEnd_symmetric h r) (typeIZYEnd_symmetric h r) t : CStarMatrix (Fin n) (Fin n) ℂ)=
          unitaryConj S (hilbertKZConnection n v (glXYEnd h r) (glZYEnd h r)
            (glXYEnd_symmetric h r) (glZYEnd_symmetric h r) t : CStarMatrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨n,v,w,S,h₁,h₂⟩ := classicalTypeI_unitary h r
  refine ⟨n,v,w,S,?_⟩
  intro t
  exact hermitianPair_KZ_intertwining n _ _ _ _
    (orthonormalMatrix_selfadjoint n v _ (glXYEnd_symmetric h r))
    (orthonormalMatrix_selfadjoint n v _ (glZYEnd_symmetric h r))
    (orthonormalMatrix_selfadjoint n w _ (typeIXYEnd_symmetric h r))
    (orthonormalMatrix_selfadjoint n w _ (typeIZYEnd_symmetric h r)) S h₁ h₂ t

/-- The corresponding Type-II reduction, including the proved same-orientation
Casimir correction by h times the identity. -/
theorem classicalTypeII_KZ (h : ℕ) (r : Fin 4 → ℕ) :
    ∃ n : ℕ,∃ v : OrthonormalBasis (Fin n) ℂ (fixedGLInvariants (K:=ℂ) (2+h) r),
      ∃ w : OrthonormalBasis (Fin n) ℂ (fixedRelativeII (K:=ℂ) h r),
        ∃ S : unitary (CStarMatrix (Fin n) (Fin n) ℂ),∀ t : ℝ,
          (hilbertKZConnection n w (typeIIXXEnd h r) (typeIIZYEnd h r)
            (typeIIXXEnd_symmetric h r) (typeIIZYEnd_symmetric h r) t : CStarMatrix (Fin n) (Fin n) ℂ)=
          unitaryConj S (hilbertKZConnection n v (glXXEnd h r) (glZYEnd h r)
            (glXXEnd_symmetric h r) (glZYEnd_symmetric h r) t : CStarMatrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨n,v,w,S,h₁,h₂⟩ := classicalTypeII_unitary h r
  refine ⟨n,v,w,S,?_⟩
  intro t
  exact hermitianPair_KZ_intertwining n _ _ _ _
    (orthonormalMatrix_selfadjoint n v _ (glXXEnd_symmetric h r))
    (orthonormalMatrix_selfadjoint n v _ (glZYEnd_symmetric h r))
    (orthonormalMatrix_selfadjoint n w _ (typeIIXXEnd_symmetric h r))
    (orthonormalMatrix_selfadjoint n w _ (typeIIZYEnd_symmetric h r)) S h₁ h₂ t

end AMSPhysical

#print axioms AMSPhysical.classicalTypeI_KZ
#print axioms AMSPhysical.classicalTypeII_KZ
