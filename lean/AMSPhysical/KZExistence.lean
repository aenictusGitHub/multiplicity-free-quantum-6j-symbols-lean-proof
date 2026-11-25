import Volterra
import KZUniqueness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

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

def residuePower (a : A) (t : ℝ) : A := NormedSpace.exp ℝ (Real.log t • a)

theorem residuePower_unitary (a : A) (ha : star a= -a) (t : ℝ) : residuePower a t∈unitary A := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ
  change star (Real.log t • a)= -(Real.log t • a)
  simp [ha,smul_neg]

theorem residuePower_inverse (a : A) (t : ℝ) : residuePower a t*endpointPower a t=1 := by
  unfold residuePower endpointPower
  have hc : Commute (Real.log t • a) ((-Real.log t) • a) :=
    ((Commute.refl a).smul_left (Real.log t)).smul_right (-Real.log t)
  rw [← NormedSpace.exp_add_of_commute hc]
  have hz : Real.log t • a+(-Real.log t) • a=0 := by module
  rw [hz,NormedSpace.exp_zero]

theorem endpointPower_inverse (a : A) (t : ℝ) : endpointPower a t*residuePower a t=1 := by
  unfold residuePower endpointPower
  have hc : Commute ((-Real.log t) • a) (Real.log t • a) :=
    ((Commute.refl a).smul_left (-Real.log t)).smul_right (Real.log t)
  rw [← NormedSpace.exp_add_of_commute hc]
  have hz : (-Real.log t) • a+Real.log t • a=0 := by module
  rw [hz,NormedSpace.exp_zero]

theorem residuePower_deriv (a : A) (t : ℝ) (ht : 0<t) :
    HasDerivAt (residuePower a) ((t⁻¹ • a)*residuePower a t) t := by
  convert (hasDerivAt_exp_smul_const' a (Real.log t)).scomp t
    (Real.hasDerivAt_log (ne_of_gt ht)) using 1
  simp [residuePower,smul_mul_assoc]

def gaugeKernel (a b : A) (t : ℝ) : A :=
  endpointPower a t*((t-1)⁻¹ • b)*residuePower a t

theorem gaugeKernel_norm (a b : A) (ha : star a= -a) (t : ℝ) :
    ‖gaugeKernel a b t‖=|t-1|⁻¹*‖b‖ := by
  unfold gaugeKernel
  rw [CStarRing.norm_mul_mem_unitary _ (residuePower_unitary a ha t),
    CStarRing.norm_mem_unitary_mul _ (endpointPower_unitary a ha t),norm_smul]
  simp

theorem gaugeKernel_bound (a b : A) (ha : star a= -a) (T : ℝ) (hT : T≤1/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) T) : ‖gaugeKernel a b t‖≤2*‖b‖ := by
  rw [gaugeKernel_norm a b ha]
  have hd : (1/2:ℝ)≤|t-1| := by
    rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)]
    linarith [ht.2]
  have hi : |t-1|⁻¹≤2 := by
    have hp : 0 < |t-1| := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hd
    exact (inv_le_iff_one_le_mul₀ hp).mpr (by linarith)
  exact mul_le_mul_of_nonneg_right hi (norm_nonneg b)

theorem gaugeKernel_continuousAt (a b : A) (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    ContinuousAt (gaugeKernel a b) t := by
  have he : Continuous (NormedSpace.exp ℝ : A → A) := NormedSpace.exp_continuous
  have hl := Real.continuousAt_log (ne_of_gt ht)
  have hne : t-1≠0 := sub_ne_zero.mpr (ne_of_lt ht1)
  exact ((he.continuousAt.comp (hl.neg.smul continuousAt_const)).mul
    (((continuousAt_id.sub continuousAt_const).inv₀ hne).smul continuousAt_const)).mul
      (he.continuousAt.comp (hl.smul continuousAt_const))

section Measurable
variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

theorem gaugeKernel_measurable (a b : A) : Measurable (gaugeKernel a b) := by
  have he : Measurable (NormedSpace.exp ℝ : A → A) := NormedSpace.exp_continuous.measurable
  have hl : Measurable Real.log := Real.measurable_log
  exact ((he.comp (hl.neg.smul_const a)).mul
    (((measurable_id.sub measurable_const).inv).smul_const b)).mul
      (he.comp (hl.smul_const a))

theorem gaugeKernel_integrable (a b : A) (ha : star a= -a) (T : ℝ) (hT : 0≤T) (hT1 : T≤1/2) :
    IntervalIntegrable (gaugeKernel a b) volume 0 T := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2*‖b‖) volume 0 T).mono_fun'
    (gaugeKernel_measurable a b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hT] at ht
  exact gaugeKernel_bound a b ha T hT1 t ⟨ht.1.le,ht.2⟩

end Measurable
end AMSPhysical

#print axioms AMSPhysical.gaugeKernel_integrable
