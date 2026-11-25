import KZExistence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Set Filter MeasureTheory
open scoped Topology

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousStar A] [StarModule ℝ A] [CStarRing A] [CompleteSpace A]

theorem residueGauge_solution (a b : A) (H : ℝ → A) (t : ℝ) (ht : 0<t)
    (hH : HasDerivAt H (gaugeKernel a b t*H t) t) :
    HasDerivAt (fun s => residuePower a s*H s)
      (realKZCoefficient a b t*(residuePower a t*H t)) t := by
  convert (residuePower_deriv a t ht).mul hH using 1
  have hc : residuePower a t*(gaugeKernel a b t*H t)=
      ((t-1)⁻¹ • b)*(residuePower a t*H t) := by
    unfold gaugeKernel
    simp only [← mul_assoc,residuePower_inverse,one_mul]
  rw [hc]
  simp only [realKZCoefficient,add_mul,mul_assoc]

theorem residueGauge_norm (a : A) (ha : star a= -a) (H : A) (t : ℝ) :
    ‖(residuePower a t*H)*endpointPower a t-1‖=‖H-1‖ := by
  have he : (residuePower a t*H)*endpointPower a t-1=
      (residuePower a t*(H-1))*endpointPower a t := by
    rw [mul_sub,mul_one,sub_mul,residuePower_inverse]
  rw [he,CStarRing.norm_mul_mem_unitary _ (endpointPower_unitary a ha t),
    CStarRing.norm_mem_unitary_mul _ (residuePower_unitary a ha t)]

theorem residueGauge_normalized (a : A) (ha : star a= -a) (H : ℝ → A)
    (hH : ContinuousAt H 0) (hH₀ : H 0=1) :
    Tendsto (fun t => (residuePower a t*H t)*endpointPower a t)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [residueGauge_norm a ha]
  have hh : Tendsto H (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa [hH₀] using hH.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun _ : ℝ => (1:A)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := tendsto_const_nhds
  simpa using (hh.sub hc).norm

section Measurable
variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

/-- Existence of a genuinely normalized KZ solution on a positive endpoint interval.
The solution is constructed by the verified Volterra fixed-point iteration. -/
theorem kz_local_normalized_exists (a b : A) (ha : star a= -a) :
    ∃ T : ℝ,0<T ∧ T≤1/2 ∧ ∃ G : ℝ → A,
      (∀ t∈Ioo (0:ℝ) T,HasDerivAt G (realKZCoefficient a b t*G t) t) ∧
      Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  let T : ℝ := 1/(4*‖b‖+4)
  have hd : 0<4*‖b‖+4 := by positivity
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1/2 := by
    dsimp [T]
    apply (div_le_iff₀ hd).mpr
    nlinarith [norm_nonneg b]
  have hsmall : T*(2*‖b‖)<1 := by
    dsimp [T]
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_lt_iff₀ hd).mpr
    nlinarith [norm_nonneg b]
  have hcK : ContinuousOn (gaugeKernel a b) (Ioo (0:ℝ) T) := by
    intro t ht
    exact (gaugeKernel_continuousAt a b t ht.1 (by linarith [ht.2])).continuousWithinAt
  obtain ⟨H,hH,hH₀,hHd⟩ := volterra_differential_exists T hT.le (gaugeKernel a b)
    (gaugeKernel_integrable a b ha T hT.le hT1) hcK 1 (2*‖b‖) (by positivity)
    (gaugeKernel_bound a b ha T hT1) hsmall
  refine ⟨T,hT,hT1,(fun t => residuePower a t*H t),?_,?_⟩
  · intro t ht
    exact residueGauge_solution a b H t ht.1 (hHd t ht)
  · exact residueGauge_normalized a ha H hH.continuousAt hH₀

end Measurable
end AMSPhysical

#print axioms AMSPhysical.kz_local_normalized_exists
