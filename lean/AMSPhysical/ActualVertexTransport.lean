import ActualPositiveVertexTable
import QuantumTypeATensorIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {V W V' W' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem tensorBilin_isometry (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (B' : LinearMap.BilinForm ℝ V') (C' : LinearMap.BilinForm ℝ W')
    (F : V →ₗ[ℝ] V') (G : W →ₗ[ℝ] W')
    (hF : ∀ v w,B' (F v) (F w)=B v w) (hG : ∀ v w,C' (G v) (G w)=C v w)
    (u v : V ⊗[ℝ] W) :
    LinearMap.BilinForm.tmul B' C' (TensorProduct.map F G u) (TensorProduct.map F G v) =
      LinearMap.BilinForm.tmul B C u v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,LinearMap.add_apply,hu,hw]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw]
    | tmul c d =>
      simp only [TensorProduct.map_tmul,LinearMap.BilinForm.tensorDistrib_tmul,hF,hG]

theorem tensorBoundary_map (e : V →ₗ[ℝ] ℝ) (f : W →ₗ[ℝ] ℝ)
    (e' : V' →ₗ[ℝ] ℝ) (f' : W' →ₗ[ℝ] ℝ) (F : V →ₗ[ℝ] V') (G : W →ₗ[ℝ] W')
    (hF : ∀ v,e' (F v)=e v) (hG : ∀ w,f' (G w)=f w) (u : V ⊗[ℝ] W) :
    f' (tensorFirstFunctional e' (TensorProduct.map F G u))=f (tensorFirstFunctional e u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul v w => simp only [TensorProduct.map_tmul,tensorFirstFunctional_tmul,map_smul,hF,hG]

variable {q : ℝ} {n : ℕ} {a b c : Fin n → ℤ}

def canonicalizeActualVertex (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space) :=
  (TensorProduct.map (A.mapTo hq (fixedActualCarrier A.irrep))
    (B.mapTo hq (fixedActualCarrier B.irrep))).comp
      (F.comp ((fixedActualCarrier C.irrep).mapTo hq C))

theorem canonicalizeActualVertex_highest (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space) :
    canonicalizeActualVertex hq A B C F (fixedActualCarrier C.irrep).frame.highest =
      TensorProduct.map (A.mapTo hq (fixedActualCarrier A.irrep))
        (B.mapTo hq (fixedActualCarrier B.irrep)) (F C.frame.highest) := by
  simp only [canonicalizeActualVertex,LinearMap.comp_apply,ActualHighestCarrier.mapTo_highest]

theorem canonicalizeActualVertex_intertwines (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space)
    (hF : ∀ z v,F (C.frame.action z v)=
      typeATensorRepresentation q hq n A.frame.action B.frame.action z (F v))
    (z : UqTypeA q n) (v : (fixedActualCarrier C.irrep).space) :
    canonicalizeActualVertex hq A B C F ((fixedActualCarrier C.irrep).frame.action z v)=
      actualVertexAction hq A.irrep B.irrep z (canonicalizeActualVertex hq A B C F v) := by
  unfold canonicalizeActualVertex
  simp only [LinearMap.comp_apply]
  rw [ActualHighestCarrier.mapTo_intertwines,hF]
  exact typeA_intertwiner_tensor q hq n A.frame.action B.frame.action
    (fixedActualCarrier A.irrep).frame.action (fixedActualCarrier B.irrep).frame.action
    (A.mapTo hq (fixedActualCarrier A.irrep)) (B.mapTo hq (fixedActualCarrier B.irrep))
    (A.mapTo_intertwines hq _) (B.mapTo_intertwines hq _) z _

theorem canonicalizeActualVertex_positive (hq : q≠0)
    (Λ : (D : ActualIrrep q n) → (fixedActualCarrier D).space →ₗ[ℝ] ℝ)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (f : B.space →ₗ[ℝ] ℝ) (hf : ∀ v,Λ B.irrep (B.mapTo hq (fixedActualCarrier B.irrep) v)=f v)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space)
    (hF : ∀ z v,F (C.frame.action z v)=
      typeATensorRepresentation q hq n A.frame.action B.frame.action z (F v))
    (hN : LinearMap.BilinForm.tmul A.frame.pairing B.frame.pairing
      (F C.frame.highest) (F C.frame.highest)=1)
    (hP : 0<f (tensorFirstFunctional (A.frame.pairing A.frame.highest) (F C.frame.highest))) :
    ActualPositiveVertex hq Λ A.irrep B.irrep C.irrep (canonicalizeActualVertex hq A B C F) := by
  refine ⟨canonicalizeActualVertex_intertwines hq A B C F hF,?_,?_⟩
  · rw [canonicalizeActualVertex_highest]
    exact (tensorBilin_isometry A.frame.pairing B.frame.pairing
      (fixedActualCarrier A.irrep).frame.pairing (fixedActualCarrier B.irrep).frame.pairing
      (A.mapTo hq _) (B.mapTo hq _) (A.mapTo_isometry hq _) (B.mapTo_isometry hq _) _ _).trans hN
  · change 0<Λ B.irrep (tensorFirstFunctional
      ((fixedActualCarrier A.irrep).frame.pairing (fixedActualCarrier A.irrep).frame.highest)
      (canonicalizeActualVertex hq A B C F (fixedActualCarrier C.irrep).frame.highest))
    rw [canonicalizeActualVertex_highest,tensorBoundary_map
      (A.frame.pairing A.frame.highest) f
      ((fixedActualCarrier A.irrep).frame.pairing (fixedActualCarrier A.irrep).frame.highest)
      (Λ B.irrep) (A.mapTo hq _) (B.mapTo hq _) (A.mapTo_highest_functional hq _) hf]
    exact hP

end AMSPhysical
#print axioms AMSPhysical.canonicalizeActualVertex_positive
