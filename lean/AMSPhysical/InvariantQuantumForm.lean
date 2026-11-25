import QuantumAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module

theorem quantumForm_basis_offDiagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (B : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] ℝ)
    (hK : PairAdjoint B (finiteQuantumK q L) (finiteQuantumK q L))
    (i j : Fin (L+1)) (hij : i≠j) : B (standardWeightBasis L i) (standardWeightBasis L j)=0 := by
  apply pairAdjoint_eigen_orthogonal hK (standardWeightBasis L i) (standardWeightBasis L j)
    (q^((L:ℤ)-2*(i.val:ℤ))) (q^((L:ℤ)-2*(j.val:ℤ)))
    (standardWeightBasis_K q L i) (standardWeightBasis_K q L j)
  intro he
  have h := zpow_right_injective₀ hq hq1 he
  apply hij
  apply Fin.ext
  omega

theorem quantumForm_basis_diagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (B : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] ℝ)
    (hE : PairAdjoint B (finiteQuantumE q L) (finiteQuantumK q L*finiteQuantumF q L))
    (i : Fin (L+1)) : B (standardWeightBasis L i) (standardWeightBasis L i)=
      B (standardWeightBasis L 0) (standardWeightBasis L 0)*quantumWeight q L i.val := by
  refine Fin.induction ?_ (fun k ih => ?_) i
  · change B (standardWeightBasis L 0) (standardWeightBasis L 0)=
      B (standardWeightBasis L 0) (standardWeightBasis L 0)*quantumWeight q L 0
    rw [quantumWeight_zero q hq,mul_one]
  · have h := hE (standardWeightBasis L k.succ) (standardWeightBasis L k.castSucc)
    change B (finiteQuantumE q L (standardWeightBasis L k.succ)) (standardWeightBasis L k.castSucc)=
      B (standardWeightBasis L k.succ) (finiteQuantumK q L (finiteQuantumF q L (standardWeightBasis L k.castSucc))) at h
    rw [standardWeightBasis_E_succ,standardWeightBasis_F_castSucc] at h
    rw [(finiteQuantumK q L).map_smul,standardWeightBasis_K,smul_smul] at h
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h
    have hc : (L:ℤ)-(k.val:ℤ)=((L-k.val:ℕ):ℤ) := by omega
    rw [hc,← qnum_eq_qInteger q hq hq1,← qnum_eq_qInteger q hq hq1,ih] at h
    have hs := quantumWeight_step q hq L k.val k.isLt
    change qnum q (k.val+1)*(B (standardWeightBasis L 0) (standardWeightBasis L 0)*quantumWeight q L k.val)=
      (qnum q (L-k.val)*q^((L:ℤ)-2*((k.val+1:ℕ):ℤ)))*B (standardWeightBasis L k.succ) (standardWeightBasis L k.succ) at h
    change B (standardWeightBasis L k.succ) (standardWeightBasis L k.succ)=
      B (standardWeightBasis L 0) (standardWeightBasis L 0)*quantumWeight q L (k.val+1)
    apply mul_left_cancel₀ (mul_ne_zero
      (ne_of_gt (qnum_pos q hq (L-k.val) (by omega)))
      (zpow_ne_zero ((L:ℤ)-2*((k.val+1:ℕ):ℤ)) (ne_of_gt hq)))
    linear_combination -h-B (standardWeightBasis L 0) (standardWeightBasis L 0)*hs

/-- Every invariant form on the constructed irreducible is a scalar multiple of the positive compact metric. -/
theorem quantumForm_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (B : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] ℝ)
    (hE : PairAdjoint B (finiteQuantumE q L) (finiteQuantumK q L*finiteQuantumF q L))
    (hK : PairAdjoint B (finiteQuantumK q L) (finiteQuantumK q L)) :
    B=B (standardWeightBasis L 0) (standardWeightBasis L 0) • quantumBilin q L := by
  apply (standardWeightBasis (K:=ℝ) L).ext
  intro i
  apply (standardWeightBasis (K:=ℝ) L).ext
  intro j
  change B (standardWeightBasis L i) (standardWeightBasis L j)=
    B (standardWeightBasis L 0) (standardWeightBasis L 0)*quantumPair q L (standardWeightBasis L i) (standardWeightBasis L j)
  rw [quantumPair_basis]
  split_ifs with hij
  · subst j
    exact quantumForm_basis_diagonal q hq hq1 L B hE i
  · rw [mul_zero]
    exact quantumForm_basis_offDiagonal q hq hq1 L B hK i j hij

end AMSPhysical

#print axioms AMSPhysical.quantumForm_unique
