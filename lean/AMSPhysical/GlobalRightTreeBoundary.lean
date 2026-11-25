import QuantumTreeBasisCoordinates
import StandardBoundaryCreationCoordinate
import StandardWeightReversal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- At a highest first input, the outer Clebsch sum has only its leading
term. Hence the remaining boundary is a single inner CG coefficient. -/
theorem quantumRightTreeHighest_first_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m c : ℕ) (p : RightHighestPath l m c) (j : Fin (m+1)) (k : Fin (c+1)) :
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (quantumRightTreeHighest q hq hq1 l m c p.1 p.2) ((0,j),k) =
      (Real.sqrt (quantumHighestNorm q l (coupledLabel m c p.1) p.2))⁻¹ *
        standardClebschCoefficient q hq hq1 m c p.1 (rightRootIndexPair l m c p 0).2 j.val k.val := by
  rw [quantumRightTreeHighest_basis_coefficient]
  congr 1
  rw [Finset.sum_eq_single (0 : Fin (p.2.val+1))]
  · simp [rightRootIndexPair,couplingBasisIndex,couplingCoefficient]
  · intro t ht ht0
    have hv : t.val≠0 := by intro he;apply ht0;exact Fin.ext he
    simp only [rightRootIndexPair,couplingBasisIndex]
    rw [if_neg (by intro he;apply hv;exact congrArg Fin.val he)]
    ring
  · simp

theorem standardTypeIIBoundaryEquiv_coordinate (a b c : ℕ)
    (v : RealQuantumTripleSpace a b c) (j : Fin (b+1)) (k : Fin (c+1)) :
    standardBoundaryCoordinate a b c j.val k.val (standardTypeIIBoundaryEquiv a b c v) =
      (((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr v ((0,j),k.rev) := by
  classical
  have he : (standardBoundaryCoordinate a b c j.val k.val).comp
      (standardTypeIIBoundaryEquiv a b c).toLinearMap =
      (Finsupp.lapply ((0,j),k.rev)).comp
        (((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).tensorProduct
          (standardWeightBasis (K:=ℝ) c)).repr.toLinearMap := by
    apply (((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).ext
    rintro ⟨⟨i,u⟩,w⟩
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Module.Basis.tensorProduct_apply',
      standardTypeIIBoundaryEquiv,LinearEquiv.trans_apply,TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul,LinearEquiv.refl_apply,standardWeightReversal_basis,
      standardBoundaryCoordinate_basis,Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self,Finsupp.single_apply]
    change (if i.val=0 ∧ u.val=j.val ∧ w.rev.val=k.val then 1 else 0) =
      (((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr
          ((standardWeightBasis a i ⊗ₜ[ℝ] standardWeightBasis b u) ⊗ₜ[ℝ] standardWeightBasis c w) ((0,j),k.rev)
    rw [← Module.Basis.tensorProduct_apply (standardWeightBasis (K:=ℝ) a) (standardWeightBasis (K:=ℝ) b) i u,
      ← Module.Basis.tensorProduct_apply ((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b))
        (standardWeightBasis (K:=ℝ) c) (i,u) w,Module.Basis.repr_self]
    simp only [Finsupp.single_apply,Prod.mk.injEq,Fin.ext_iff,Fin.val_zero]
    have hr : w.rev.val=k.val ↔ w.val=k.rev.val := by
      simpa only [← Fin.ext_iff] using (Fin.rev_eq_iff (i:=w) (j:=k))
    simp only [hr]
    by_cases hi : i.val=0 <;> by_cases hu : u.val=j.val <;>
      by_cases hw : w.val=k.rev.val <;> simp_all
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.quantumRightTreeHighest_first_coordinate
#print axioms AMSPhysical.standardTypeIIBoundaryEquiv_coordinate
