import QuantumOrthonormalBasis
import QuantumIntertwinerSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem quantumHighest_orthogonal_lower (q : ℝ) (hq : 0<q) (hq1 : q≠1) (H L : ℕ)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hB : ∀ p v,B p v=B v p)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) (hρ : IsCompactQuantumPair q B ρ)
    (p : W) (hE : ρ (uqGenerator q 0) p=0) (hK : ρ (uqGenerator q 2) p=q^(H:ℤ) • p)
    (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T)
    (k : Fin L) : B p (T (standardWeightBasis L k.succ))=0 := by
  have hKi := representation_Kinv_eigen q ρ (q^(H:ℤ)) (zpow_ne_zero _ (ne_of_gt hq)) p hK
  have hEKi : ρ (uqGenerator q 0) (ρ (uqGenerator q 3) p)=0 := by
    rw [hKi,map_smul,hE,smul_zero]
  have hg : finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q 1)=
      finiteQuantumF q L := finiteQuantumRepresentation_generator q (ne_of_gt hq)
        (qInteger_denominator_ne_zero q hq hq1) L 1
  have hF : ρ (uqGenerator q 1) (T (standardWeightBasis L k.castSucc))=
      qInteger q ((L:ℤ)-(k.val:ℤ)) • T (standardWeightBasis L k.succ) := by
    rw [hT (uqGenerator q 1) _,hg,standardWeightBasis_F_castSucc,T.map_smul]
  have he := hρ.adjF (T (standardWeightBasis L k.castSucc)) p
  change B (ρ (uqGenerator q 1) (T (standardWeightBasis L k.castSucc))) p=
    B (T (standardWeightBasis L k.castSucc)) (ρ (uqGenerator q 0) (ρ (uqGenerator q 3) p)) at he
  rw [hF,hEKi,(B (T (standardWeightBasis L k.castSucc))).map_zero] at he
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at he
  have hn : qInteger q ((L:ℤ)-(k.val:ℤ))≠0 := ne_of_gt (qInteger_pos_real q hq hq1 _ (by omega))
  rw [hB p (T (standardWeightBasis L k.succ))]
  exact (mul_eq_zero.mp he).resolve_left hn

theorem quantumHighest_orthogonal_orthonormalLower (q : ℝ) (hq : 0<q) (hq1 : q≠1) (H L : ℕ)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hB : ∀ p v,B p v=B v p)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) (hρ : IsCompactQuantumPair q B ρ)
    (p : W) (hE : ρ (uqGenerator q 0) p=0) (hK : ρ (uqGenerator q 2) p=q^(H:ℤ) • p)
    (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T)
    (k : Fin L) : B p (T (orthonormalWeightVector q L k.succ))=0 := by
  unfold orthonormalWeightVector
  rw [T.map_smul,(B p).map_smul,smul_eq_mul,
    quantumHighest_orthogonal_lower (W:=W) q hq hq1 H L B hB ρ hρ p hE hK T hT k,mul_zero]

end AMSPhysical

#print axioms AMSPhysical.quantumHighest_orthogonal_orthonormalLower
