import ActualVertexTreeCoherence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {q : ℝ} {n : ℕ} {a b c d e : Fin n → ℤ}

theorem canonicalizeActualVertex_smul (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space) (s : ℝ) :
    canonicalizeActualVertex hq A B C (s • F)=s • canonicalizeActualVertex hq A B C F := by
  apply LinearMap.ext
  intro v
  simp only [canonicalizeActualVertex,LinearMap.comp_apply,LinearMap.smul_apply,map_smul]

theorem actualLeftVertexTree_of_entries (hq : q≠0) (T : ActualVertexTable q n)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b)
    (C : ActualHighestCarrier q n c) (D : ActualHighestCarrier q n d) (E : ActualHighestCarrier q n e)
    (F : E.space →ₗ[ℝ] A.space ⊗[ℝ] B.space) (G : D.space →ₗ[ℝ] E.space ⊗[ℝ] C.space)
    (hF : T A.irrep B.irrep E.irrep=canonicalizeActualVertex hq A B E F)
    (hG : T E.irrep C.irrep D.irrep=canonicalizeActualVertex hq E C D G) :
    actualLeftVertexTree T A.irrep B.irrep C.irrep D.irrep E.irrep (fixedActualCarrier D.irrep).frame.highest =
      canonicalizeActualTriple hq A B C ((TensorProduct.assoc ℝ A.space B.space C.space)
        (TensorProduct.map F LinearMap.id (G D.frame.highest))) := by
  unfold actualLeftVertexTree
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hF,hG,canonicalizeActualVertex_left_tree hq A B C D E F G,
    ActualHighestCarrier.mapTo_highest]

theorem actualRightVertexTree_of_entries (hq : q≠0) (T : ActualVertexTable q n)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b)
    (C : ActualHighestCarrier q n c) (D : ActualHighestCarrier q n d) (E : ActualHighestCarrier q n e)
    (F : E.space →ₗ[ℝ] B.space ⊗[ℝ] C.space) (G : D.space →ₗ[ℝ] A.space ⊗[ℝ] E.space)
    (hF : T B.irrep C.irrep E.irrep=canonicalizeActualVertex hq B C E F)
    (hG : T A.irrep E.irrep D.irrep=canonicalizeActualVertex hq A E D G) :
    actualRightVertexTree T A.irrep B.irrep C.irrep D.irrep E.irrep (fixedActualCarrier D.irrep).frame.highest =
      canonicalizeActualTriple hq A B C (TensorProduct.map LinearMap.id F (G D.frame.highest)) := by
  unfold actualRightVertexTree
  simp only [LinearMap.comp_apply]
  rw [hF,hG,canonicalizeActualVertex_right_tree hq A B C D E F G,
    ActualHighestCarrier.mapTo_highest]

end AMSPhysical
#print axioms AMSPhysical.actualLeftVertexTree_of_entries
#print axioms AMSPhysical.actualRightVertexTree_of_entries
