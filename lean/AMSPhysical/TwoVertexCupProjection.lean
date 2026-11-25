import TwoVertexPairProjection
import QuantumSymmetricDualAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexTensorProjection_coordinate (n : ℕ) (hn : 0<n) (l m : ℕ)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (i : Fin (l+1)) (j : Fin (m+1)) :
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (twoVertexTensorProjection n hn l m w) (i,j)=
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).repr w
      (twoVertexOccupation n hn l i,twoVertexOccupation n hn m j) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w z hw hz => simp only [map_add,Finsupp.add_apply,hw,hz]
  | tmul u v =>
    change ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (TensorProduct.map _ _ (u ⊗ₜ[ℝ] v)) (i,j)=_
    rw [TensorProduct.map_tmul,Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.tensorProduct_repr_tmul_apply]
    change (standardWeightBasis (K:=ℝ) m).equivFun (twoVertexProjection n hn m v) j*
      (standardWeightBasis (K:=ℝ) l).equivFun (twoVertexProjection n hn l u) i=
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).equivFun v (twoVertexOccupation n hn m j)*
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).equivFun u (twoVertexOccupation n hn l i)
    rw [twoVertexProjection_coordinate,twoVertexProjection_coordinate]

theorem twoVertexOccupation_dual_sign (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    occupationDualSign n L (twoVertexOccupation n hn L k)=(-1:ℝ)^(k.val:ℤ) := by
  unfold occupationDualSign
  congr 1
  unfold occupationHeightZ latticePairing twoVertexOccupation
  simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  simp [Pi.single_apply,mul_ite,Finset.sum_ite_eq',secondVertex]

/-- The literal physical cup restricts to the same standard two-coordinate
cup in EVERY rank; no rank-dependent scalar is hidden in this equation. -/
theorem symmetricCoevaluation_twoVertex_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (L : ℕ) :
    twoVertexTensorProjection n hn L L (symmetricCoevaluation q n L)=
      diagonalCoevaluation (standardWeightBasis (K:=ℝ) L)
        (fun k =>(-1:ℝ)^(k.val:ℤ)/quantumWeight q L k.val) := by
  apply ((standardWeightBasis (K:=ℝ) L).tensorProduct (standardWeightBasis (K:=ℝ) L)).repr.injective
  ext ij
  rcases ij with ⟨i,j⟩
  rw [twoVertexTensorProjection_coordinate,symmetricCoevaluation_diagonal,
    diagonalCoevaluation_coordinate,diagonalCoevaluation_coordinate,
    twoVertexOccupation_dual_sign,twoVertexOccupation_weight q hq hq1]
  simp only [(twoVertexOccupation_injective n hn L).eq_iff]

end AMSPhysical
#print axioms AMSPhysical.symmetricCoevaluation_twoVertex_projection
