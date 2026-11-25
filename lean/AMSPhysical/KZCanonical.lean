import Bielecki
import KZLocal
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Set Filter MeasureTheory
open scoped Topology ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousStar A] [StarModule ℝ A] [CStarRing A] [CompleteSpace A]

theorem gaugeKernel_bound_threequarters (a b : A) (ha : star a= -a)
    (t : ℝ) (ht : t∈Icc (0:ℝ) (3/4)) : ‖gaugeKernel a b t‖≤4*‖b‖ := by
  rw [gaugeKernel_norm a b ha]
  have hd : (1/4:ℝ)≤|t-1| := by
    rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)]
    linarith [ht.2]
  have hi : |t-1|⁻¹≤4 :=
    (inv_le_iff_one_le_mul₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hd)).mpr (by linarith)
  exact mul_le_mul_of_nonneg_right hi (norm_nonneg b)

section Measurable
variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

theorem gaugeKernel_integrable_threequarters (a b : A) (ha : star a= -a) :
    IntervalIntegrable (gaugeKernel a b) volume 0 (3/4) := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 4*‖b‖) volume 0 (3/4)).mono_fun'
    (gaugeKernel_measurable a b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤3/4)] at ht
  exact gaugeKernel_bound_threequarters a b ha t ⟨ht.1.le,ht.2⟩

/-- A constructed normalized endpoint solution extending past the common reference point 1/2. -/
theorem kz_normalized_exists (a b : A) (ha : star a= -a) :
    ∃ G : ℝ → A,
      (∀ t∈Ioo (0:ℝ) (3/4),HasDerivAt G (realKZCoefficient a b t*G t) t) ∧
      Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  let T : ℝ := 3/4
  have hT : 0≤T := by norm_num [T]
  have hK := gaugeKernel_integrable_threequarters a b ha
  obtain ⟨H,hH⟩ := volterra_exists T hT (gaugeKernel a b) hK 1 (4*‖b‖) (by positivity)
    (gaugeKernel_bound_threequarters a b ha)
  let H' := intervalExtend T hT H
  have hH₀ : H' 0=1 := volterra_solution_initial T hT (gaugeKernel a b) 1 H hH
  have hcont : Continuous H' := intervalExtend_continuous T hT H
  refine ⟨(fun t => residuePower a t*H' t),?_,residueGauge_normalized a ha H' hcont.continuousAt hH₀⟩
  intro t ht
  apply residueGauge_solution a b H' t ht.1
  exact volterra_solution_deriv T hT (gaugeKernel a b) hK 1 H hH t ht
    (gaugeKernel_continuousAt a b t ht.1 (by linarith [ht.2]))

end Measurable

theorem skew_ode_gram_constant_on (T : ℝ) (a : ℝ → A) (G : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) T,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) T,HasDerivAt G (a x*G x) x)
    (x y : ℝ) (hx : x∈Ioo (0:ℝ) T) (hy : y∈Ioo (0:ℝ) T) :
    star (G x)*G x=star (G y)*G y := by
  have hd (t : ℝ) (ht : t∈Ioo (0:ℝ) T) := skew_ode_gram_deriv (a t) (ha t ht) G t (hG t ht)
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) T).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hx hy

theorem unitary_normalizer_gram_norm (G R : A) (hR : R∈unitary A) :
    ‖star (G*R)*(G*R)-1‖=‖star G*G-1‖ := by
  have he : star (G*R)*(G*R)-1=star R*(star G*G-1)*R := by
    have hr : star R*R=1 := (unitary.mem_iff.mp hR).1
    simp only [star_mul,mul_sub,sub_mul,mul_one,hr]
    noncomm_ring
  rw [he,CStarRing.norm_mul_mem_unitary _ hR,
    CStarRing.norm_mem_unitary_mul _ (unitary.star_mem hR)]

theorem normalized_skew_solution_isometry (T : ℝ) (hT : 0<T) (a : ℝ → A) (G R : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) T,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) T,HasDerivAt G (a x*G x) x)
    (hR : ∀ x∈Ioo (0:ℝ) T,R x∈unitary A)
    (h₀ : Tendsto (fun t => G t*R t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) T) : star (G x)*G x=1 := by
  have hconst : Tendsto (fun _ : ℝ => (1:A)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := tendsto_const_nhds
  have hlim : Tendsto (fun t => ‖star (G t*R t)*(G t*R t)-1‖)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((h₀.star.mul h₀).sub hconst).norm
  have he : (fun t => ‖star (G t*R t)*(G t*R t)-1‖)=ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun _ => ‖star (G x)*G x-1‖) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    rw [unitary_normalizer_gram_norm _ _ (hR t ht),skew_ode_gram_constant_on T a G ha hG t x ht hx]
  have hz : ‖star (G x)*G x-1‖=0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' he)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem matrix_isometry_unitary (n : ℕ) (G : CStarMatrix (Fin n) (Fin n) ℂ)
    (hG : star G*G=1) : G∈unitary (CStarMatrix (Fin n) (Fin n) ℂ) := by
  rw [unitary.mem_iff]
  refine ⟨hG,?_⟩
  exact Matrix.mul_eq_one_comm.mp hG

/-- The constructed normalized matrix KZ solution is genuinely unitary. -/
theorem matrix_kz_normalized_exists (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) :
    ∃ G : ℝ → CStarMatrix (Fin n) (Fin n) ℂ,
      (∀ t∈Ioo (0:ℝ) (3/4),HasDerivAt G (realKZCoefficient a b t*G t) t) ∧
      Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1) ∧
      ∀ t∈Ioo (0:ℝ) (3/4),G t∈unitary (CStarMatrix (Fin n) (Fin n) ℂ) := by
  letI : FiniteDimensional ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin n → Fin n → ℂ))
  letI : MeasurableSpace (CStarMatrix (Fin n) (Fin n) ℂ) := borel _
  letI : BorelSpace (CStarMatrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
  obtain ⟨G,hG,h₀⟩ := kz_normalized_exists a b ha
  refine ⟨G,hG,h₀,?_⟩
  intro t ht
  apply matrix_isometry_unitary n
  exact normalized_skew_solution_isometry (3/4) (by norm_num) (realKZCoefficient a b) G (endpointPower a)
    (fun x _ => realKZCoefficient_skew a b ha hb x) hG (fun x _ => endpointPower_unitary a ha x) h₀ t ht

end AMSPhysical

#print axioms AMSPhysical.matrix_kz_normalized_exists
