import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousStar A] [StarModule ℝ A]

theorem skew_ode_gram_deriv (a : A) (ha : star a= -a) (G : ℝ → A) (x : ℝ)
    (hG : HasDerivAt G (a*G x) x) :
    HasDerivAt (fun t => star (G t)*G t) 0 x := by
  convert hG.star.mul hG using 1
  rw [star_mul,ha]
  noncomm_ring

/-- The Gram operator of a skew-adjoint ODE solution is constant on (0,1). -/
theorem skew_ode_gram_constant (a : ℝ → A) (G : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) 1,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt G (a x*G x) x)
    (x y : ℝ) (hx : x∈Ioo (0:ℝ) 1) (hy : y∈Ioo (0:ℝ) 1) :
    star (G x)*G x=star (G y)*G y := by
  have hd (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) := skew_ode_gram_deriv (a t) (ha t ht) G t (hG t ht)
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hx hy

variable [CStarRing A]

/-- A skew-adjoint solution with zero right endpoint limit is identically zero.
This handles the singular endpoint by norm conservation, rather than by assuming
an ordinary initial-value theorem at that singular point. -/
theorem skew_ode_zero_of_endpoint (a : ℝ → A) (G : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) 1,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt G (a x*G x) x)
    (h₀ : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : G x=0 := by
  have hlim : Tendsto (fun t => star (G t)*G t) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using h₀.star.mul h₀
  have he : (fun t => star (G t)*G t)=ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun _ => star (G x)*G x) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    exact skew_ode_gram_constant a G ha hG t x ht hx
  have hz : star (G x)*G x=0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' he)
  exact (CStarRing.star_mul_self_eq_zero_iff _).mp hz

theorem skew_ode_unique_endpoint (a : ℝ → A) (G H : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) 1,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt G (a x*G x) x)
    (hH : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt H (a x*H x) x)
    (h₀ : Tendsto (fun t => G t-H t) (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : G x=H x := by
  apply sub_eq_zero.mp
  apply skew_ode_zero_of_endpoint a (fun t => G t-H t) ha _ h₀ x hx
  intro t ht
  simpa only [mul_sub] using (hG t ht).sub (hH t ht)

def realKZCoefficient (a b : A) (t : ℝ) : A := t⁻¹ • a+(t-1)⁻¹ • b

theorem realKZCoefficient_skew (a b : A) (ha : star a= -a) (hb : star b= -b) (t : ℝ) :
    star (realKZCoefficient a b t)= -realKZCoefficient a b t := by
  simp [realKZCoefficient,ha,hb,smul_neg,add_comm]

/-- Any common unitary endpoint normalization determines at most one solution. -/
theorem skew_ode_unique_normalized (a : ℝ → A) (G H R : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) 1,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt G (a x*G x) x)
    (hH : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt H (a x*H x) x)
    (hR : ∀ x∈Ioo (0:ℝ) 1,R x∈unitary A)
    (h₀G : Tendsto (fun t => G t*R t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (h₀H : Tendsto (fun t => H t*R t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : G x=H x := by
  apply skew_ode_unique_endpoint a G H ha hG hH _ x hx
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun t => (G t-H t)*R t) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [sub_mul,sub_self] using h₀G.sub h₀H
  have hn := hlim.norm
  have he : (fun t => ‖(G t-H t)*R t‖)=ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun t => ‖G t-H t‖) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    exact CStarRing.norm_mul_mem_unitary _ (hR t ht)
  simpa using hn.congr' he

variable [CompleteSpace A]

def endpointPower (a : A) (t : ℝ) : A := NormedSpace.exp ℝ ((-Real.log t) • a)

theorem endpointPower_unitary (a : A) (ha : star a= -a) (t : ℝ) :
    endpointPower a t∈unitary A := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ
  change star ((-Real.log t) • a)= -((-Real.log t) • a)
  simp [ha,smul_neg]

/-- Uniqueness for the normalized KZ equation with genuine skew-adjoint residues. -/
theorem kz_normalized_unique (a b : A) (ha : star a= -a) (hb : star b= -b)
    (G H : ℝ → A)
    (hG : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt G (realKZCoefficient a b x*G x) x)
    (hH : ∀ x∈Ioo (0:ℝ) 1,HasDerivAt H (realKZCoefficient a b x*H x) x)
    (h₀G : Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (h₀H : Tendsto (fun t => H t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : G x=H x :=
  skew_ode_unique_normalized (realKZCoefficient a b) G H (endpointPower a)
    (fun t _ => realKZCoefficient_skew a b ha hb t) hG hH
    (fun t _ => endpointPower_unitary a ha t) h₀G h₀H x hx

end AMSPhysical

#print axioms AMSPhysical.skew_ode_unique_endpoint
