import QuantumClebschOrthogonality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module

theorem finiteQuantum_commuting_scalar (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (A : Module.End ℝ (finiteWeightSpace (K:=ℝ) L)) (c : ℝ)
    (hAF : A*finiteQuantumF q L=finiteQuantumF q L*A)
    (h0 : A (standardWeightBasis L 0)=c • standardWeightBasis L 0)
    (v : finiteWeightSpace (K:=ℝ) L) : A v=c • v := by
  have hb (i : Fin (L+1)) : A (standardWeightBasis L i)=c • standardWeightBasis L i := by
    refine Fin.induction h0 (fun k ih => ?_) i
    have h := congrArg (fun T : Module.End ℝ (finiteWeightSpace (K:=ℝ) L) => T (standardWeightBasis L k.castSucc)) hAF
    change A (finiteQuantumF q L (standardWeightBasis L k.castSucc))=
      finiteQuantumF q L (A (standardWeightBasis L k.castSucc)) at h
    rw [standardWeightBasis_F_castSucc,ih,A.map_smul,(finiteQuantumF q L).map_smul,standardWeightBasis_F_castSucc] at h
    have hn : qInteger q ((L:ℤ)-(k.val:ℤ))≠0 :=
      ne_of_gt (qInteger_pos_real q hq hq1 _ (by omega))
    have hc := congrArg (fun w => (qInteger q ((L:ℤ)-(k.val:ℤ)))⁻¹ • w) h
    dsimp only at hc
    rw [smul_comm c,smul_smul,inv_mul_cancel₀ hn,one_smul,smul_smul,inv_mul_cancel₀ hn,one_smul] at hc
    exact hc
  have he : A=c • (1 : Module.End ℝ (finiteWeightSpace (K:=ℝ) L)) := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro i
    exact hb i
  exact DFunLike.congr_fun he v

theorem finiteQuantumCasimir_scalar (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (v : finiteWeightSpace (K:=ℝ) L) :
    finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L (uqCasimir q) v=
      quantumCasimirEigen q L • v := by
  let ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ (finiteWeightSpace (K:=ℝ) L) :=
    finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L
  have hg (i : Fin 4) : ρ (uqGenerator q i)=
      ![finiteQuantumE q L,finiteQuantumF q L,finiteQuantumK q L,finiteQuantumKinv q L] i :=
    finiteQuantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L i
  apply finiteQuantum_commuting_scalar q hq hq1 L (ρ (uqCasimir q)) (quantumCasimirEigen q L)
  · have h := congrArg ρ (uqCasimir_commutes_F q (ne_of_gt hq))
    rw [map_mul,map_mul,hg 1] at h
    exact h
  · apply representation_Casimir_highest q (ne_of_gt hq) ρ L (standardWeightBasis L 0)
    · rw [hg 0]
      exact standardWeightBasis_E_zero q L
    · rw [hg 2]
      have h := standardWeightBasis_K q L (0 : Fin (L+1))
      simpa only [Fin.val_zero,Nat.cast_zero,mul_zero,sub_zero] using h

end AMSPhysical

#print axioms AMSPhysical.finiteQuantumCasimir_scalar
