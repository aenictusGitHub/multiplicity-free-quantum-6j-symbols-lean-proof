import AMSOuterVerticesFullIsometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {q : ℝ} {n : ℕ} {a b c : Fin n → ℤ}

structure ActualUnitaryVertex (hq : q≠0) (A B C : ActualIrrep q n)
    (F : (fixedActualCarrier C).space →ₗ[ℝ] (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space) : Prop where
  intertwines : ∀ z v,F ((fixedActualCarrier C).frame.action z v)=actualVertexAction hq A B z (F v)
  isometry : ∀ v w,actualVertexPair A B (F v) (F w)=(fixedActualCarrier C).frame.pairing v w

theorem canonicalizeActualVertex_isometry (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space)
    (hF : ∀ v w,LinearMap.BilinForm.tmul A.frame.pairing B.frame.pairing (F v) (F w)=C.frame.pairing v w)
    (v w : (fixedActualCarrier C.irrep).space) :
    actualVertexPair A.irrep B.irrep (canonicalizeActualVertex hq A B C F v)
      (canonicalizeActualVertex hq A B C F w)=(fixedActualCarrier C.irrep).frame.pairing v w := by
  unfold canonicalizeActualVertex actualVertexPair
  simp only [LinearMap.comp_apply]
  calc
    _ = LinearMap.BilinForm.tmul A.frame.pairing B.frame.pairing
        (F ((fixedActualCarrier C.irrep).mapTo hq C v))
        (F ((fixedActualCarrier C.irrep).mapTo hq C w)) :=
      tensorBilin_isometry A.frame.pairing B.frame.pairing
        (fixedActualCarrier A.irrep).frame.pairing (fixedActualCarrier B.irrep).frame.pairing
        (A.mapTo hq _) (B.mapTo hq _) (A.mapTo_isometry hq _) (B.mapTo_isometry hq _) _ _
    _ = C.frame.pairing ((fixedActualCarrier C.irrep).mapTo hq C v)
        ((fixedActualCarrier C.irrep).mapTo hq C w) := hF _ _
    _ = _ := (fixedActualCarrier C.irrep).mapTo_isometry hq C v w

theorem canonicalizeActualVertex_unitary (hq : q≠0)
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (C : ActualHighestCarrier q n c)
    (F : C.space →ₗ[ℝ] A.space ⊗[ℝ] B.space)
    (hF : ∀ z v,F (C.frame.action z v)=typeATensorRepresentation q hq n A.frame.action B.frame.action z (F v))
    (hIso : ∀ v w,LinearMap.BilinForm.tmul A.frame.pairing B.frame.pairing (F v) (F w)=C.frame.pairing v w)
    (e : ℝ) (he : e*e=1) :
    ActualUnitaryVertex hq A.irrep B.irrep C.irrep (e • canonicalizeActualVertex hq A B C F) := by
  constructor
  · intro z v
    simp only [LinearMap.smul_apply]
    rw [canonicalizeActualVertex_intertwines hq A B C F hF,map_smul]
  · intro v w
    simp only [LinearMap.smul_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [canonicalizeActualVertex_isometry hq A B C F hIso]
    calc
      _ = (e*e)*(fixedActualCarrier C.irrep).frame.pairing v w := by ring
      _ = _ := by rw [he,one_mul]

end AMSPhysical
#print axioms AMSPhysical.canonicalizeActualVertex_unitary
