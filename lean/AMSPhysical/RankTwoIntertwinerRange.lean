import RankTwoSymmetricEquivalence
import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- A genuine finite sl2 intertwiner lands in any invariant submodule that
contains its highest vector. All weight vectors are reached using actual F. -/
theorem rankTwoIntertwiner_range_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (ρ : UqTypeA q 1 →ₐ[ℝ] Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : ∀ z v,T (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L
      (rankTwoToSL2 q z) v)=ρ z (T v))
    (S : Submodule ℝ W) (hS : algebraInvariant ρ S)
    (h0 : T (standardWeightBasis L 0)∈S) (v : finiteWeightSpace (K:=ℝ) L) : T v∈S := by
  have hF (w : finiteWeightSpace (K:=ℝ) L) :
      T (finiteQuantumF q L w)=ρ (typeAAlgebraGenerator q 1 0 1) (T w) := by
    have hh:=hT (typeAAlgebraGenerator q 1 0 1) w
    rw [rankTwoToSL2_generator] at hh
    change T (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L
      (RingQuot.mkAlgHom ℝ (QuantumSL2Relation q) (FreeAlgebra.ι ℝ 1)) w)=_ at hh
    rw [finiteQuantumRepresentation_generator] at hh
    exact hh
  have hb (k : Fin (L+1)) : T (standardWeightBasis L k)∈S := by
    induction k using Fin.induction with
    | zero => exact h0
    | succ k ih =>
      have hh:=hS (typeAAlgebraGenerator q 1 0 1) _ ih
      rw [← hF,standardWeightBasis_F_castSucc,map_smul] at hh
      have hnonzero : qInteger q ((L:ℤ)-(k.val:ℤ))≠0 :=
        ne_of_gt (qInteger_pos_real q hq hq1 _ (by have hk:=k.isLt;omega))
      have hs:=S.smul_mem (qInteger q ((L:ℤ)-(k.val:ℤ)))⁻¹ hh
      simpa only [smul_smul,inv_mul_cancel₀ hnonzero,one_smul] using hs
  rw [← (standardWeightBasis (K:=ℝ) L).sum_repr v,map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  exact S.smul_mem _ (hb i)

theorem rankTwoIntertwiner_highest_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (L : ℕ)
    (ρ : UqTypeA q 1 →ₐ[ℝ] Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : ∀ z v,T (finiteQuantumRepresentation q hq hD L (rankTwoToSL2 q z) v)=ρ z (T v)) :
    ρ (typeAAlgebraGenerator q 1 0 0) (T (standardWeightBasis L 0))=0 := by
  rw [← hT,rankTwoToSL2_generator]
  change T (finiteQuantumRepresentation q hq hD L
    (RingQuot.mkAlgHom ℝ (QuantumSL2Relation q) (FreeAlgebra.ι ℝ 0)) (standardWeightBasis L 0))=0
  rw [finiteQuantumRepresentation_generator]
  change T (finiteQuantumE q L (standardWeightBasis L 0))=0
  rw [standardWeightBasis_E_zero,map_zero]

theorem rankTwoIntertwiner_highest_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (L : ℕ)
    (ρ : UqTypeA q 1 →ₐ[ℝ] Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : ∀ z v,T (finiteQuantumRepresentation q hq hD L (rankTwoToSL2 q z) v)=ρ z (T v)) :
    ρ (typeAAlgebraGenerator q 1 0 2) (T (standardWeightBasis L 0))=q^(L:ℤ) • T (standardWeightBasis L 0) := by
  rw [← hT,rankTwoToSL2_generator]
  change T (finiteQuantumRepresentation q hq hD L
    (RingQuot.mkAlgHom ℝ (QuantumSL2Relation q) (FreeAlgebra.ι ℝ 2)) (standardWeightBasis L 0))=_
  rw [finiteQuantumRepresentation_generator]
  change T (finiteQuantumK q L (standardWeightBasis L 0))=_
  rw [standardWeightBasis_K]
  simp only [Fin.val_zero,Nat.cast_zero,mul_zero,sub_zero,map_smul]

end AMSPhysical
#print axioms AMSPhysical.rankTwoIntertwiner_range_mem
