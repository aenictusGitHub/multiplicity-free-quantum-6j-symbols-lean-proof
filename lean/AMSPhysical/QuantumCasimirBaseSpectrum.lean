import QuantumCasimir
import QuantumPositive

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

def quantumCasimirEigen (q : K) (L : ℤ) : K := q^(L+1)+q^(-(L+1))

theorem representation_Kinv_eigen {V : Type*} [AddCommGroup V] [Module K V]
    (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V) (eigenScalar : K) (heigenScalar : eigenScalar≠0)
    (v : V) (hv : ρ (uqGenerator q 2) v=eigenScalar • v) :
    ρ (uqGenerator q 3) v=eigenScalar⁻¹ • v := by
  have h := congrArg (ρ (uqGenerator q 3)) hv
  change ρ (uqGenerator q 3) (ρ (uqGenerator q 2) v)=ρ (uqGenerator q 3) (eigenScalar • v) at h
  have hi : ρ (uqGenerator q 3) (ρ (uqGenerator q 2) v)=v := by
    rw [← Module.End.mul_apply,← map_mul,uq_inverse',map_one,Module.End.one_apply]
  rw [hi,map_smul] at h
  calc
    ρ (uqGenerator q 3) v=(eigenScalar⁻¹*eigenScalar) • (ρ (uqGenerator q 3) v) := by rw [inv_mul_cancel₀ heigenScalar,one_smul]
    _=eigenScalar⁻¹ • (eigenScalar • (ρ (uqGenerator q 3) v)) := (smul_smul _ _ _).symm
    _=eigenScalar⁻¹ • v := by rw [← h]

theorem representation_Casimir_highest {V : Type*} [AddCommGroup V] [Module K V]
    (q : K) (hq : q≠0) (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℤ)
    (v : V) (hE : ρ (uqGenerator q 0) v=0) (hK : ρ (uqGenerator q 2) v=q^L • v) :
    ρ (uqCasimir q) v=quantumCasimirEigen q L • v := by
  have hKi := representation_Kinv_eigen q ρ (q^L) (zpow_ne_zero _ hq) v hK
  simp only [uqCasimir,map_add,map_smul,map_mul,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.mul_apply,hE,map_zero,hK,hKi,smul_zero,zero_add,smul_smul]
  rw [← add_smul]
  congr 1
  simp only [quantumCasimirEigen,zpow_add₀ hq,zpow_one,neg_add,zpow_neg]
  ring

theorem quantumCasimirEigen_injective_real (q : ℝ) (hq : 0<q) (hq1 : q≠1) :
    Set.InjOn (quantumCasimirEigen q) (Set.Ici (0:ℤ)) := by
  intro L hL M hM he
  let a := q^(L+1)
  let b := q^(M+1)
  have ha : a≠0 := zpow_ne_zero _ (ne_of_gt hq)
  have hb : b≠0 := zpow_ne_zero _ (ne_of_gt hq)
  have he' : a+a⁻¹=b+b⁻¹ := by simpa only [quantumCasimirEigen,zpow_neg] using he
  have hf : (a-b)*(a*b-1)=0 := by
    field_simp [ha,hb] at he'
    linear_combination he'
  have hab : a*b≠1 := by
    change q^(L+1)*q^(M+1)≠1
    rw [← zpow_add₀ (ne_of_gt hq)]
    intro hh
    have hz := (zpow_eq_one_iff_right₀ hq.le hq1).mp hh
    have hL0 : 0≤L := hL
    have hM0 : 0≤M := hM
    omega
  have heq : a=b := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (sub_ne_zero.mpr hab))
  have hexp := zpow_right_injective₀ hq hq1 heq
  omega

end AMSPhysical

#print axioms AMSPhysical.representation_Casimir_highest
#print axioms AMSPhysical.quantumCasimirEigen_injective_real
