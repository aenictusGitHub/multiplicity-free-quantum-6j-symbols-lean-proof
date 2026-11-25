import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace AMSPhysical

section Algebra
variable {A : Type*} [Ring A] [StarRing A]

/-- Selfadjoint intertwining implies commutation of the Gram operator. -/
theorem gram_commutes (a b f : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hf : b*f=f*a) : Commute (star f*f) a := by
  have hstar : star f*b=a*star f := by
    simpa only [star_mul,ha.star_eq,hb.star_eq] using congrArg star hf
  show (star f*f)*a=a*(star f*f)
  calc
    (star f*f)*a=star f*(f*a) := mul_assoc _ _ _
    _=star f*(b*f) := by rw [hf]
    _=(star f*b)*f := (mul_assoc _ _ _).symm
    _=(a*star f)*f := by rw [hstar]
    _=a*(star f*f) := mul_assoc _ _ _

omit [StarRing A] in
theorem corrected_intertwiner (a b f q : A) (hf : b*f=f*a) (hq : Commute q a) :
    b*(f*q)=(f*q)*a := by
  calc
    b*(f*q)=(b*f)*q := (mul_assoc _ _ _).symm
    _=(f*a)*q := by rw [hf]
    _=f*(a*q) := mul_assoc _ _ _
    _=f*(q*a) := by rw [hq.eq]
    _=(f*q)*a := (mul_assoc _ _ _).symm

end Algebra

section FunctionalCalculus
variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℝ A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-- A simultaneous polar unitary exists for any two selfadjoint intertwining pairs.
The positive square root is constructed by Mathlib's continuous functional calculus;
its existence is not an additional hypothesis of this theorem. -/
theorem exists_simultaneous_unitary (a₁ a₂ b₁ b₂ f : A) (hf : IsUnit f)
    (ha₁ : IsSelfAdjoint a₁) (ha₂ : IsSelfAdjoint a₂)
    (hb₁ : IsSelfAdjoint b₁) (hb₂ : IsSelfAdjoint b₂)
    (h₁ : b₁*f=f*a₁) (h₂ : b₂*f=f*a₂) :
    ∃ s : A, s ∈ unitary A ∧ b₁*s=s*a₁ ∧ b₂*s=s*a₂ := by
  let g := star f*f
  have hg : 0≤g := star_mul_self_nonneg f
  have hgunit : IsUnit g := hf.star.mul hf
  have hhunit : IsUnit (CFC.sqrt g) := (CFC.isUnit_sqrt_iff g hg).mpr hgunit
  obtain ⟨u,hu⟩ := hhunit
  have hsquare : (u:A)*(u:A)=g := by
    rw [hu]
    exact CFC.sqrt_mul_sqrt_self g hg
  have hstaru : star u=u := by
    apply Units.ext
    change star (u:A)=(u:A)
    rw [hu]
    exact (CFC.sqrt_nonneg g).isSelfAdjoint.star_eq
  let q : A := ↑(u⁻¹)
  have hstarq : star q=q := by
    change (↑(star (u⁻¹)):A)=↑(u⁻¹)
    rw [star_inv,hstaru]
  have hnorm : q*g*q=1 := by
    rw [← hsquare]
    simp [q]
  have hqcomm (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
      (h : b*f=f*a) : Commute q a := by
    have hc : Commute g a := gram_commutes a b f ha hb h
    have hs : Commute (CFC.sqrt g) a := by
      rw [CFC.sqrt_eq_cfc]
      exact hc.cfc_nnreal NNReal.sqrt
    have hucomm : Commute (u:A) a := by simpa only [hu] using hs
    exact hucomm.units_inv_left
  refine ⟨f*q,?_,corrected_intertwiner _ _ _ _ h₁ (hqcomm a₁ b₁ ha₁ hb₁ h₁),
    corrected_intertwiner _ _ _ _ h₂ (hqcomm a₂ b₂ ha₂ hb₂ h₂)⟩
  apply (hf.mul (u⁻¹).isUnit).mem_unitary_of_star_mul_self
  change star (f*q)*(f*q)=1
  simpa only [star_mul,hstarq,mul_assoc,g] using hnorm

end FunctionalCalculus
end AMSPhysical

#print axioms AMSPhysical.gram_commutes
#print axioms AMSPhysical.exists_simultaneous_unitary
