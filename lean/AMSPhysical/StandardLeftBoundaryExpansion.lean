import StandardWeightReversal
import QuantumHighestNorm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Complete independent standard left-tree expansion in the physical
opposite-leg boundary coordinates. -/
theorem standardLeftTreeHighest_boundary_expansion (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c:ℕ)
    (s:Fin (min a b+1)) (u:Fin (min (coupledLabel a b s) c+1)):
    standardTypeIIBoundaryEquiv a b c (quantumLeftTreeHighest q hq hq1 a b c s u)=
      ∑ t:Fin (u.val+1),
        ((Real.sqrt (quantumHighestNorm q (coupledLabel a b s) c u))⁻¹*
          couplingCoefficient q (c:ℤ) u.val t.val) •
        (TensorProduct.assoc ℝ _ _ _)
          (unitaryQuantumClebschMap q hq hq1 a b s
            (standardWeightBasis (coupledLabel a b s) ⟨t.val,by have ht:=t.isLt;have hu:=channel_left_bound (coupledLabel a b s) c u;omega⟩)
              ⊗ₜ[ℝ] standardWeightBasis c ⟨c-u.val+t.val,by
                have ht:=t.isLt
                have hu:=channel_right_bound (coupledLabel a b s) c u
                omega⟩) := by
  unfold quantumLeftTreeHighest quantumLeftTreeMap
  rw [standardTypeIIBoundaryEquiv_before_assoc]
  change (TensorProduct.assoc ℝ _ _ _)
    (TensorProduct.map _ _ (TensorProduct.map _ _
      ((Real.sqrt (quantumHighestNorm q (coupledLabel a b s) c u))⁻¹ •
        quantumClebschMap q hq hq1 (coupledLabel a b s) c u
          (standardWeightBasis (coupledLabel (coupledLabel a b s) c u) 0))))=_
  rw [quantumClebschMap_highest q hq hq1,finiteCoupledHighest_basis]
  simp only [map_smul,map_sum,Module.Basis.tensorProduct_apply',TensorProduct.map_tmul,
    Module.End.one_apply,LinearMap.id_apply,LinearEquiv.coe_coe,standardWeightReversal_basis,TensorProduct.assoc_tmul,
    TensorProduct.tmul_smul,← TensorProduct.smul_tmul',Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro t ht
  have he : (couplingBasisIndex (coupledLabel a b s) c u.val
      (channel_left_bound (coupledLabel a b s) c u)
      (channel_right_bound (coupledLabel a b s) c u) t).2.rev =
      (⟨c-u.val+t.val,by have ht:=t.isLt;have hu:=channel_right_bound (coupledLabel a b s) c u;omega⟩:Fin (c+1)) := by
    apply Fin.ext
    simp only [Fin.val_rev,Fin.val_mk,couplingBasisIndex]
    have hti:=t.isLt
    have hu:=channel_right_bound (coupledLabel a b s) c u
    omega
  rw [he]
  rfl

end AMSPhysical
#print axioms AMSPhysical.standardLeftTreeHighest_boundary_expansion
