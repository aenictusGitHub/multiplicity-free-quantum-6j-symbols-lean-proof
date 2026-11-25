import SharedActualAMSVertexTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {q : ℝ} {n : ℕ} {a b c d e : Fin n → ℤ}

def canonicalizeActualTriple (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c) :=
  TensorProduct.map (A.mapTo hq (fixedActualCarrier A.irrep))
    (TensorProduct.map (B.mapTo hq (fixedActualCarrier B.irrep)) (C.mapTo hq (fixedActualCarrier C.irrep)))

def actualLeftVertexTree (T : ActualVertexTable q n) (A B C D E : ActualIrrep q n) :=
  (TensorProduct.assoc ℝ (fixedActualCarrier A).space (fixedActualCarrier B).space
    (fixedActualCarrier C).space).toLinearMap.comp
    ((TensorProduct.map (T A B E) (LinearMap.id : (fixedActualCarrier C).space →ₗ[ℝ] _)).comp (T E C D))

def actualRightVertexTree (T : ActualVertexTable q n) (A B C D E : ActualIrrep q n) :=
  (TensorProduct.map (LinearMap.id : (fixedActualCarrier A).space →ₗ[ℝ] _) (T B C E)).comp (T A E D)

theorem ActualHighestCarrier.mapTo_roundtrip (hq : q≠0)
    (E F : ActualHighestCarrier q n e) (v : E.space) : F.mapTo hq E (E.mapTo hq F v)=v := by
  have he:=DFunLike.congr_fun (E.mapTo_comp hq F E) v
  rw [E.mapTo_self] at he
  simpa only [LinearMap.comp_apply,LinearMap.id_apply] using he

/-- Changing an internal actual carrier cancels between the two vertices
of the left tree. Only the common external transport remains. -/
theorem canonicalizeActualVertex_left_tree (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b)
    (C : ActualHighestCarrier q n c) (D : ActualHighestCarrier q n d) (E : ActualHighestCarrier q n e)
    (F : E.space →ₗ[ℝ] A.space ⊗[ℝ] B.space) (G : D.space →ₗ[ℝ] E.space ⊗[ℝ] C.space)
    (x : (fixedActualCarrier D.irrep).space) :
    (TensorProduct.assoc ℝ (fixedActualCarrier A.irrep).space (fixedActualCarrier B.irrep).space
      (fixedActualCarrier C.irrep).space)
      (TensorProduct.map (canonicalizeActualVertex hq A B E F) LinearMap.id
        (canonicalizeActualVertex hq E C D G x)) =
    canonicalizeActualTriple hq A B C ((TensorProduct.assoc ℝ A.space B.space C.space)
      (TensorProduct.map F LinearMap.id (G ((fixedActualCarrier D.irrep).mapTo hq D x)))) := by
  have hCancel (v : E.space ⊗[ℝ] C.space) :
      TensorProduct.map (canonicalizeActualVertex hq A B E F) LinearMap.id
        (TensorProduct.map (E.mapTo hq (fixedActualCarrier E.irrep)) (C.mapTo hq (fixedActualCarrier C.irrep)) v) =
      TensorProduct.map (TensorProduct.map (A.mapTo hq (fixedActualCarrier A.irrep))
        (B.mapTo hq (fixedActualCarrier B.irrep))) (C.mapTo hq (fixedActualCarrier C.irrep))
        (TensorProduct.map F LinearMap.id v) := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw]
    | tmul v w =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,canonicalizeActualVertex,LinearMap.comp_apply,
        ActualHighestCarrier.mapTo_roundtrip]
  change (TensorProduct.assoc ℝ _ _ _)
    (TensorProduct.map (canonicalizeActualVertex hq A B E F) LinearMap.id
      (TensorProduct.map (E.mapTo hq (fixedActualCarrier E.irrep)) (C.mapTo hq (fixedActualCarrier C.irrep))
        (G ((fixedActualCarrier D.irrep).mapTo hq D x)))) = _
  rw [hCancel]
  exact (TensorProduct.map_map_assoc (A.mapTo hq _) (B.mapTo hq _) (C.mapTo hq _) _).symm

/-- The same cancellation holds in the right tree, including coincident
Dynkin descriptions used in different AMS roles. -/
theorem canonicalizeActualVertex_right_tree (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b)
    (C : ActualHighestCarrier q n c) (D : ActualHighestCarrier q n d) (E : ActualHighestCarrier q n e)
    (F : E.space →ₗ[ℝ] B.space ⊗[ℝ] C.space) (G : D.space →ₗ[ℝ] A.space ⊗[ℝ] E.space)
    (x : (fixedActualCarrier D.irrep).space) :
    TensorProduct.map LinearMap.id (canonicalizeActualVertex hq B C E F)
      (canonicalizeActualVertex hq A E D G x) =
      canonicalizeActualTriple hq A B C
        (TensorProduct.map LinearMap.id F (G ((fixedActualCarrier D.irrep).mapTo hq D x))) := by
  have hCancel (v : A.space ⊗[ℝ] E.space) :
      TensorProduct.map LinearMap.id (canonicalizeActualVertex hq B C E F)
        (TensorProduct.map (A.mapTo hq (fixedActualCarrier A.irrep)) (E.mapTo hq (fixedActualCarrier E.irrep)) v) =
      canonicalizeActualTriple hq A B C (TensorProduct.map LinearMap.id F v) := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw]
    | tmul v w =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,canonicalizeActualVertex,LinearMap.comp_apply,
        canonicalizeActualTriple,ActualHighestCarrier.mapTo_roundtrip]
  exact hCancel (G ((fixedActualCarrier D.irrep).mapTo hq D x))

theorem canonicalizeActualTriple_isometry (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (v w : A.space ⊗[ℝ] (B.space ⊗[ℝ] C.space)) :
    LinearMap.BilinForm.tmul (fixedActualCarrier A.irrep).frame.pairing
      (LinearMap.BilinForm.tmul (fixedActualCarrier B.irrep).frame.pairing (fixedActualCarrier C.irrep).frame.pairing)
      (canonicalizeActualTriple hq A B C v) (canonicalizeActualTriple hq A B C w)=
      LinearMap.BilinForm.tmul A.frame.pairing (LinearMap.BilinForm.tmul B.frame.pairing C.frame.pairing) v w := by
  exact tensorBilin_isometry A.frame.pairing (LinearMap.BilinForm.tmul B.frame.pairing C.frame.pairing)
    (fixedActualCarrier A.irrep).frame.pairing
    (LinearMap.BilinForm.tmul (fixedActualCarrier B.irrep).frame.pairing (fixedActualCarrier C.irrep).frame.pairing)
    (A.mapTo hq _) (TensorProduct.map (B.mapTo hq _) (C.mapTo hq _)) (A.mapTo_isometry hq _)
    (tensorBilin_isometry B.frame.pairing C.frame.pairing (fixedActualCarrier B.irrep).frame.pairing
      (fixedActualCarrier C.irrep).frame.pairing (B.mapTo hq _) (C.mapTo hq _)
      (B.mapTo_isometry hq _) (C.mapTo_isometry hq _)) v w

end AMSPhysical
#print axioms AMSPhysical.canonicalizeActualVertex_left_tree
#print axioms AMSPhysical.canonicalizeActualVertex_right_tree
#print axioms AMSPhysical.canonicalizeActualTriple_isometry
