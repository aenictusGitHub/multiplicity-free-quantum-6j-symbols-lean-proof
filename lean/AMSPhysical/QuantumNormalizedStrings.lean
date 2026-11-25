import QuantumStrings
import QuantumClebschClosed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Standard highest-weight normalization of a constructed lowering string. -/
def normalizedString (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V)
    (L : ℕ) (v : V) (k : ℕ) : V :=
  (qFalling q L k)⁻¹ • (((ρ (uqGenerator q 1))^k) v)

theorem normalizedString_zero (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V)
    (L : ℕ) (v : V) : normalizedString q ρ L v 0=v := by
  simp only [normalizedString,qFalling,inv_one,pow_zero,Module.End.one_apply,one_smul]

theorem normalizedString_weight (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℕ) (v : V)
    (hK : ρ (uqGenerator q 2) v=q^(L:ℤ) • v) (k : ℕ) :
    ρ (uqGenerator q 2) (normalizedString q ρ L v k)=
      q^((L:ℤ)-2*k) • normalizedString q ρ L v k := by
  simp only [normalizedString,map_smul]
  rw [representation_K_Fpow q hq ρ L v hK,smul_smul,smul_smul,mul_comm]

theorem normalizedString_F_succ (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V)
    (L : ℕ) (v : V) (k : ℕ) (hk : k<L)
    (hqi : ∀ j : ℤ,0<j → j≤(L:ℤ) → qInteger q j≠0) :
    ρ (uqGenerator q 1) (normalizedString q ρ L v k)=
      qInteger q ((L:ℤ)-k) • normalizedString q ρ L v (k+1) := by
  have hf : qFalling q L k≠0 := qFalling_ne_zero q L k (by omega) hqi
  have hc : qInteger q ((L:ℤ)-k)≠0 := hqi _ (by omega) (by omega)
  simp only [normalizedString,map_smul,qFalling,smul_smul]
  rw [pow_succ',Module.End.mul_apply]
  congr 1
  field_simp

theorem normalizedString_E_succ (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℕ) (v : V)
    (hE : ρ (uqGenerator q 0) v=0) (hK : ρ (uqGenerator q 2) v=q^(L:ℤ) • v)
    (k : ℕ) (hk : k<L) (hqi : ∀ j : ℤ,0<j → j≤(L:ℤ) → qInteger q j≠0) :
    ρ (uqGenerator q 0) (normalizedString q ρ L v (k+1))=
      qInteger q (k+1:ℕ) • normalizedString q ρ L v k := by
  have hf : qFalling q L k≠0 := qFalling_ne_zero q L k (by omega) hqi
  have hc : qInteger q ((L:ℤ)-k)≠0 := hqi _ (by omega) (by omega)
  simp only [normalizedString,map_smul]
  rw [representation_E_Fpow_succ q hq hd ρ L v hE hK k,qFalling,smul_smul,smul_smul]
  congr 1
  field_simp

theorem normalizedString_E_zero (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V)
    (L : ℕ) (v : V) (hE : ρ (uqGenerator q 0) v=0) :
    ρ (uqGenerator q 0) (normalizedString q ρ L v 0)=0 := by
  rw [normalizedString_zero,hE]

theorem normalizedString_F_top (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V)
    (L : ℕ) (v : V) (hF : ((ρ (uqGenerator q 1))^(L+1)) v=0) :
    ρ (uqGenerator q 1) (normalizedString q ρ L v L)=0 := by
  rw [normalizedString,map_smul,← Module.End.mul_apply,← pow_succ',hF,smul_zero]

end AMSPhysical

#print axioms AMSPhysical.normalizedString_E_succ
#print axioms AMSPhysical.normalizedString_F_succ
