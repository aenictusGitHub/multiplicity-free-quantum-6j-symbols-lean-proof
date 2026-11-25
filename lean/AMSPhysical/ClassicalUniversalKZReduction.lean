import ClassicalUniversalIntertwining

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

theorem hilbertKZConnection_mapped_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (n : ℕ) (v : OrthonormalBasis (Fin n) ℂ E) (e : E ≃ₗᵢ[ℂ] F)
    (A B : Module.End ℂ E) (A' B' : Module.End ℂ F)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hA' : A'.IsSymmetric) (hB' : B'.IsSymmetric)
    (hAA' : ∀ x,A' (e x)=e (A x)) (hBB' : ∀ x,B' (e x)=e (B x)) (t : ℝ) :
    hilbertKZConnection n (v.map e) A' B' hA' hB' t=hilbertKZConnection n v A B hA hB t := by
  have ha:=orthonormalMatrix_mapped_isometry n v e A A' hAA'
  have hb:=orthonormalMatrix_mapped_isometry n v e B B' hBB'
  unfold hilbertKZConnection
  simp only [ha,hb]

/-- Complete classical Type-I KZ transport using the literal normalized
determinant map F/sqrt(h!(h+1)!), with no polar-decomposition choice. -/
theorem classicalUniversalI_KZ (h : ℕ) (r : Fin 4 → ℕ) (n : ℕ)
    (v : OrthonormalBasis (Fin n) ℂ (fixedGLInvariants (K:=ℂ) (2+h) r)) (t : ℝ) :
    hilbertKZConnection n (v.map (classicalUniversalIsometryI h r))
      (typeIXYEnd h r) (typeIZYEnd h r) (typeIXYEnd_symmetric h r) (typeIZYEnd_symmetric h r) t=
      hilbertKZConnection n v (glXYEnd h r) (glZYEnd h r)
        (glXYEnd_symmetric h r) (glZYEnd_symmetric h r) t := by
  apply hilbertKZConnection_mapped_isometry
  · intro p
    exact (classicalUniversalI_XY h r p).symm
  · intro p
    exact (classicalUniversalI_ZY h r p).symm

/-- The corresponding explicit full Type-II classical KZ transport, with
the actual same-orientation Casimir correction already included. -/
theorem classicalUniversalII_KZ (h : ℕ) (r : Fin 4 → ℕ) (n : ℕ)
    (v : OrthonormalBasis (Fin n) ℂ (fixedGLInvariants (K:=ℂ) (2+h) r)) (t : ℝ) :
    hilbertKZConnection n (v.map (classicalUniversalIsometryII h r))
      (typeIIXXEnd h r) (typeIIZYEnd h r) (typeIIXXEnd_symmetric h r) (typeIIZYEnd_symmetric h r) t=
      hilbertKZConnection n v (glXXEnd h r) (glZYEnd h r)
        (glXXEnd_symmetric h r) (glZYEnd_symmetric h r) t := by
  apply hilbertKZConnection_mapped_isometry
  · intro p
    exact (classicalUniversalII_XX h r p).symm
  · intro p
    exact (classicalUniversalII_ZY h r p).symm

end AMSPhysical
#print axioms AMSPhysical.classicalUniversalI_KZ
#print axioms AMSPhysical.classicalUniversalII_KZ
