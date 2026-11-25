import InvariantFFT
import PolynomialWeight
import Mathlib.LinearAlgebra.Determinant
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def familyCharge (n : ℕ) : Fin 4×Fin n → ℤ := fun ai => ![1,1,-1,-1] ai.1

def IsSpecialLinearInvariant (n : ℕ) (p : PN K n) : Prop :=
  ∀ g : Vec K n ≃ₗ[K] Vec K n, LinearMap.det g.toLinearMap=1 →
    ∀ v,eval (pointAction n g v) p=eval v p

def normalizedEquiv (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n) (t : K) (ht : t≠0) :
    Vec K n ≃ₗ[K] Vec K n :=
  g.trans (LinearEquiv.smulOfNeZero K (Vec K n) t⁻¹ (inv_ne_zero ht))

theorem normalizedEquiv_linearMap (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (t : K) (ht : t≠0) :
    (normalizedEquiv n g t ht).toLinearMap=t⁻¹ • g.toLinearMap := by
  ext v i
  simp [normalizedEquiv]

theorem normalizedEquiv_det (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (t : K) (ht : t≠0) (hs : t^n=LinearMap.det g.toLinearMap) :
    LinearMap.det (normalizedEquiv n g t ht).toLinearMap=1 := by
  rw [normalizedEquiv_linearMap,LinearMap.det_smul,Module.finrank_fin_fun]
  rw [← hs,inv_pow,inv_mul_cancel₀ (pow_ne_zero n ht)]

theorem normalizedEquiv_symm (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (t : K) (ht : t≠0) (u : Vec K n) :
    (normalizedEquiv n g t ht).symm u=t • g.symm u := by
  apply (normalizedEquiv n g t ht).injective
  simp [normalizedEquiv,Units.smul_def,smul_smul,ht]

theorem pointAction_normalize (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (t : K) (ht : t≠0) (v : Fin 4×Fin n → K) :
    pointAction n g v=weightScale (familyCharge n) t
      (pointAction n (normalizedEquiv n g t ht) v) := by
  funext ⟨a,i⟩
  fin_cases a <;> simp [pointAction,weightScale,familyCharge,normalizedEquiv_symm,
    normalizedEquiv,Units.smul_def,smul_eq_mul,ht]

theorem balanced_sl_invariant_is_gl [IsAlgClosed K] (n : ℕ) (hn : 0<n)
    (p : PN K n) (hp : IsSpecialLinearInvariant n p)
    (hw : HasPolynomialWeight (familyCharge n) 0 p) : IsGLInvariant n p := by
  intro g v
  have hD : LinearMap.det g.toLinearMap≠0 := g.isUnit_det'.ne_zero
  obtain ⟨t,hts⟩ := IsAlgClosed.exists_pow_nat_eq (LinearMap.det g.toLinearMap) hn
  have ht : t≠0 := by intro hz; rw [hz,zero_pow (Nat.ne_of_gt hn)] at hts; exact hD hts.symm
  rw [pointAction_normalize n g t ht,eval_weightScale _ _ _ hw t ht]
  simp only [zpow_zero,one_mul]
  exact hp (normalizedEquiv n g t ht) (normalizedEquiv_det n g t ht hts) v

def HasFamilyDegrees (n : ℕ) (r : Fin 4 → ℤ) (p : PN K n) : Prop :=
  ∀ m∈p.support,∀ a,∑ i : Fin n,(m (a,i):ℤ)=r a

theorem family_degrees_charge (n : ℕ) (r : Fin 4 → ℤ) (p : PN K n)
    (hp : HasFamilyDegrees n r p) :
    HasPolynomialWeight (familyCharge n) (r 0+r 1-r 2-r 3) p := by
  intro m hm
  simp [exponentWeight,familyCharge,Fintype.sum_prod_type,Fin.sum_univ_succ]
  rw [hp m hm 0,hp m hm 1,hp m hm 2,hp m hm 3]
  ring

theorem balanced_sl_reconstruction [Infinite K] [IsAlgClosed K] (h : ℕ)
    (r : Fin 4 → ℤ) (p : PN K (2+h)) (hp : IsSpecialLinearInvariant (2+h) p)
    (hd : HasFamilyDegrees (2+h) r p) (hbal : r 0+r 1=r 2+r 3) :
    p=pullN (2+h) (covBackN h p) := by
  apply gl_invariant_reconstruction h p
  apply balanced_sl_invariant_is_gl (2+h) (by omega) p hp
  have hw := family_degrees_charge (2+h) r p hd
  have hz : r 0+r 1-r 2-r 3=0 := by omega
  simpa [hz] using hw

end AMSPhysical

#print axioms AMSPhysical.balanced_sl_reconstruction
