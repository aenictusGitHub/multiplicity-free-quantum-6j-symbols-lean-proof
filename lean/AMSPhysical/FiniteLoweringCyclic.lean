import QuantumClebschIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Maps from a finite physical sl2 module that commute with lowering are
already determined by their value on the actual highest generator. -/
theorem finiteQuantumF_cyclic_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (A : Module.End ℝ W) (T S : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : ∀ v,T (finiteQuantumF q L v)=A (T v))
    (hS : ∀ v,S (finiteQuantumF q L v)=A (S v))
    (h0 : T (standardWeightBasis L 0)=S (standardWeightBasis L 0)) : T=S := by
  have hb (i : Fin (L+1)) : T (standardWeightBasis L i)=S (standardWeightBasis L i) := by
    refine Fin.induction h0 (fun k ih =>?_) i
    have he:=(hT (standardWeightBasis L k.castSucc)).trans
      ((congrArg A ih).trans (hS (standardWeightBasis L k.castSucc)).symm)
    rw [standardWeightBasis_F_castSucc,map_smul,map_smul] at he
    have hc : qInteger q ((L:ℤ)-(k.val:ℤ))≠0:=ne_of_gt (qInteger_pos_real q hq hq1 _ (by omega))
    have hi:=congrArg (fun w : W =>(qInteger q ((L:ℤ)-(k.val:ℤ)))⁻¹ • w) he
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi
  exact (standardWeightBasis (K:=ℝ) L).ext hb

theorem finiteQuantumF_range_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (A : Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : ∀ v,T (finiteQuantumF q L v)=A (T v)) (S : Submodule ℝ W)
    (hS : ∀ w∈S,A w∈S) (h0 : T (standardWeightBasis L 0)∈S)
    (v : finiteWeightSpace (K:=ℝ) L) : T v∈S := by
  have hb (i : Fin (L+1)) : T (standardWeightBasis L i)∈S := by
    refine Fin.induction h0 (fun k ih =>?_) i
    have he:=hT (standardWeightBasis L k.castSucc)
    rw [standardWeightBasis_F_castSucc,map_smul] at he
    have hm : qInteger q ((L:ℤ)-(k.val:ℤ)) • T (standardWeightBasis L k.succ)∈S := by
      rw [he]
      exact hS _ ih
    have hc : qInteger q ((L:ℤ)-(k.val:ℤ))≠0:=ne_of_gt (qInteger_pos_real q hq hq1 _ (by omega))
    have hi:=S.smul_mem (qInteger q ((L:ℤ)-(k.val:ℤ)))⁻¹ hm
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi
  have he:= (standardWeightBasis (K:=ℝ) L).sum_repr v
  rw [← he,map_sum]
  exact S.sum_mem (fun i _ =>by rw [map_smul];exact S.smul_mem _ (hb i))

end AMSPhysical
#print axioms AMSPhysical.finiteQuantumF_cyclic_unique
#print axioms AMSPhysical.finiteQuantumF_range_mem
