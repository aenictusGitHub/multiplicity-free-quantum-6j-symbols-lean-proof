import QuantumRecouplingConstruction
import QuantumTripleMetric
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def standardWeightReversal (L:ℕ):finiteWeightSpace (K:=ℝ) L ≃ₗ[ℝ] finiteWeightSpace (K:=ℝ) L:=
  (standardWeightBasis (K:=ℝ) L).equiv (standardWeightBasis (K:=ℝ) L) Fin.revPerm

theorem standardWeightReversal_basis (L:ℕ) (k:Fin (L+1)):
    standardWeightReversal L (standardWeightBasis L k)=standardWeightBasis L k.rev :=
  Module.Basis.equiv_apply _ _ _ _

def standardTypeIIBoundaryEquiv (a b c:ℕ):RealQuantumTripleSpace a b c ≃ₗ[ℝ]
    (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)):=
  (TensorProduct.assoc ℝ _ _ _).trans
    (TensorProduct.congr (LinearEquiv.refl ℝ _) (TensorProduct.congr (LinearEquiv.refl ℝ _) (standardWeightReversal c)))

theorem standardTypeIIBoundaryEquiv_before_assoc (a b c:ℕ) (v:RealQuantumTripleSpace a b c):
    standardTypeIIBoundaryEquiv a b c v=(TensorProduct.assoc ℝ _ _ _)
      (TensorProduct.map (LinearMap.id:Module.End ℝ (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] finiteWeightSpace (K:=ℝ) b))
        (standardWeightReversal c).toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul u v =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [TensorProduct.add_tmul,map_add,hu,hu']
    | tmul x y =>
      simp only [standardTypeIIBoundaryEquiv,LinearEquiv.trans_apply,TensorProduct.assoc_tmul,
        TensorProduct.congr_tmul,LinearEquiv.refl_apply,TensorProduct.map_tmul,LinearMap.id_apply,LinearEquiv.coe_coe]

end AMSPhysical
#print axioms AMSPhysical.standardTypeIIBoundaryEquiv_before_assoc
