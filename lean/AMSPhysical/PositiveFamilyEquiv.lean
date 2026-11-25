import RangeGramEquivalence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {I V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def positiveFamilyEquiv (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (v : I → V) (w : I → W) (h : ∀ i j,B (v i) (v j)=C (w i) (w j)) :
    Submodule.span ℝ (Set.range v) ≃ₗ[ℝ] Submodule.span ℝ (Set.range w) :=
  ((LinearEquiv.ofEq _ _ (Finsupp.range_linearCombination ℝ (v:=v))).symm.trans
    (sameKernelRangeEquiv (Finsupp.linearCombination ℝ v) (Finsupp.linearCombination ℝ w)
      (linearCombination_kernels_eq B C hB hC v w h))).trans
    (LinearEquiv.ofEq _ _ (Finsupp.range_linearCombination ℝ (v:=w)))

theorem positiveFamilyEquiv_combination (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (v : I → V) (w : I → W) (h : ∀ i j,B (v i) (v j)=C (w i) (w j))
    (f : I →₀ ℝ) (hf : Finsupp.linearCombination ℝ v f∈Submodule.span ℝ (Set.range v)) :
    (positiveFamilyEquiv B C hB hC v w h ⟨Finsupp.linearCombination ℝ v f,hf⟩).val=
      Finsupp.linearCombination ℝ w f := by
  unfold positiveFamilyEquiv
  simp only [LinearEquiv.trans_apply,LinearEquiv.ofEq_symm,LinearEquiv.coe_ofEq_apply]
  have he : (LinearEquiv.ofEq (Submodule.span ℝ (Set.range v))
      (LinearMap.range (Finsupp.linearCombination ℝ v))
      (Finsupp.range_linearCombination ℝ (v:=v)).symm)
      ⟨Finsupp.linearCombination ℝ v f,hf⟩=
      ⟨Finsupp.linearCombination ℝ v f,⟨f,rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [he]
  exact sameKernelRangeEquiv_image _ _ _ f _

/-- Positive Gram realizations have a constructed isometry on their entire
spans, even if their displayed spanning families have linear relations. -/
theorem positiveFamilyEquiv_isometry (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (v : I → V) (w : I → W) (h : ∀ i j,B (v i) (v j)=C (w i) (w j))
    (x y : Submodule.span ℝ (Set.range v)) :
    B x.val y.val=C (positiveFamilyEquiv B C hB hC v w h x).val
      (positiveFamilyEquiv B C hB hC v w h y).val := by
  have hx : x.val∈LinearMap.range (Finsupp.linearCombination ℝ v) := by rw [Finsupp.range_linearCombination];exact x.property
  have hy : y.val∈LinearMap.range (Finsupp.linearCombination ℝ v) := by rw [Finsupp.range_linearCombination];exact y.property
  obtain ⟨f,hf⟩ := hx
  obtain ⟨g,hg⟩ := hy
  have hx' : x=⟨Finsupp.linearCombination ℝ v f,by rw [hf];exact x.property⟩ := Subtype.ext hf.symm
  have hy' : y=⟨Finsupp.linearCombination ℝ v g,by rw [hg];exact y.property⟩ := Subtype.ext hg.symm
  rw [hx',hy',positiveFamilyEquiv_combination,positiveFamilyEquiv_combination]
  exact linearCombination_pair_congr B C v w h f g

end AMSPhysical
#print axioms AMSPhysical.positiveFamilyEquiv_isometry
