import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Set Filter MeasureTheory intervalIntegral
open scoped Topology NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def intervalExtend (T : ℝ) (hT : 0≤T) (H : C(Icc (0:ℝ) T,A)) (t : ℝ) : A :=
  H (projIcc 0 T hT t)

theorem intervalExtend_continuous (T : ℝ) (hT : 0≤T) (H : C(Icc (0:ℝ) T,A)) :
    Continuous (intervalExtend T hT H) := H.continuous.comp continuous_projIcc

theorem kernel_product_integrable (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (H : C(Icc (0:ℝ) T,A)) :
    IntervalIntegrable (fun s => K s*intervalExtend T hT H s) volume 0 T :=
  hK.mul_continuousOn (intervalExtend_continuous T hT H).continuousOn

/-- The actual Volterra integral iteration, including integrable kernels that
need not have a continuous extension to the endpoint. -/
def volterraStep (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (H : C(Icc (0:ℝ) T,A)) :
    C(Icc (0:ℝ) T,A) where
  toFun t := y₀+∫ s in 0..t.val,K s*intervalExtend T hT H s
  continuous_toFun := by
    have hc := continuousOn_primitive_interval' (kernel_product_integrable T hT K hK H)
      (left_mem_uIcc : (0:ℝ)∈uIcc 0 T)
    rw [uIcc_of_le hT] at hc
    exact continuous_const.add (continuousOn_iff_continuous_restrict.mp hc)

theorem volterraStep_lipschitz (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (M : ℝ) (hM : 0≤M)
    (hbound : ∀ s∈Icc (0:ℝ) T,‖K s‖≤M) (H G : C(Icc (0:ℝ) T,A)) :
    ‖volterraStep T hT K hK y₀ H-volterraStep T hT K hK y₀ G‖≤(T*M)*‖H-G‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg hT hM) (norm_nonneg _))).mpr
  intro x
  have hsub : uIcc (0:ℝ) x.val⊆uIcc (0:ℝ) T := by
    rw [uIcc_of_le x.property.1,uIcc_of_le hT]
    exact Icc_subset_Icc_right x.property.2
  have hH := (kernel_product_integrable T hT K hK H).mono_set hsub
  have hG := (kernel_product_integrable T hT K hK G).mono_set hsub
  change ‖(y₀+∫ s in 0..x.val,K s*intervalExtend T hT H s)-
    (y₀+∫ s in 0..x.val,K s*intervalExtend T hT G s)‖≤_
  rw [add_sub_add_left_eq_sub,← integral_sub hH hG]
  have hnorm : ‖∫ s in 0..x.val,
      (K s*intervalExtend T hT H s-K s*intervalExtend T hT G s)‖≤
        (M*‖H-G‖)*|x.val-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hsT : s∈Icc (0:ℝ) T := by
      rw [uIoc_of_le x.property.1] at hs
      exact ⟨hs.1.le,hs.2.trans x.property.2⟩
    rw [← mul_sub]
    calc
      ‖K s*(intervalExtend T hT H s-intervalExtend T hT G s)‖≤
          ‖K s‖*‖intervalExtend T hT H s-intervalExtend T hT G s‖ := norm_mul_le _ _
      _≤M*‖H-G‖ := mul_le_mul (hbound s hsT)
        (ContinuousMap.norm_coe_le_norm (H-G) (projIcc 0 T hT s))
        (norm_nonneg _) hM
  calc
    _≤(M*‖H-G‖)*|x.val-0| := hnorm
    _≤(M*‖H-G‖)*T := by
      rw [sub_zero,abs_of_nonneg x.property.1]
      exact mul_le_mul_of_nonneg_left x.property.2 (mul_nonneg hM (norm_nonneg _))
    _=(T*M)*‖H-G‖ := by ring

/-- Existence is obtained from Banach's fixed-point theorem, not postulated. -/
theorem volterra_exists_small (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (M : ℝ) (hM : 0≤M)
    (hbound : ∀ s∈Icc (0:ℝ) T,‖K s‖≤M) (hsmall : T*M<1) :
    ∃ H : C(Icc (0:ℝ) T,A), ∀ t : Icc (0:ℝ) T,
      H t=y₀+∫ s in 0..t.val,K s*intervalExtend T hT H s := by
  let L : ℝ≥0 := ⟨T*M,mul_nonneg hT hM⟩
  have hc : ContractingWith L (volterraStep T hT K hK y₀) := by
    refine ⟨hsmall,?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro H G
    simpa only [dist_eq_norm] using volterraStep_lipschitz T hT K hK y₀ M hM hbound H G
  let H := hc.fixedPoint
  refine ⟨H,?_⟩
  intro t
  have he := congrArg (fun F : C(Icc (0:ℝ) T,A) => F t) hc.fixedPoint_isFixedPt.eq
  exact he.symm

theorem volterra_solution_initial (T : ℝ) (hT : 0≤T) (K : ℝ → A) (y₀ : A)
    (H : C(Icc (0:ℝ) T,A))
    (hH : ∀ t : Icc (0:ℝ) T,H t=y₀+∫ s in 0..t.val,K s*intervalExtend T hT H s) :
    intervalExtend T hT H 0=y₀ := by
  have he := hH ⟨0,⟨le_rfl,hT⟩⟩
  simpa [intervalExtend,projIcc_of_mem] using he

theorem volterra_solution_deriv (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (H : C(Icc (0:ℝ) T,A))
    (hH : ∀ t : Icc (0:ℝ) T,H t=y₀+∫ s in 0..t.val,K s*intervalExtend T hT H s)
    (x : ℝ) (hx : x∈Ioo (0:ℝ) T) (hcK : ContinuousAt K x) :
    HasDerivAt (intervalExtend T hT H) (K x*intervalExtend T hT H x) x := by
  have hprod := kernel_product_integrable T hT K hK H
  have hsub : uIcc (0:ℝ) x⊆uIcc (0:ℝ) T := by
    rw [uIcc_of_le hx.1.le,uIcc_of_le hT]
    exact Icc_subset_Icc_right hx.2.le
  have hm : StronglyMeasurableAtFilter (fun s => K s*intervalExtend T hT H s) (nhds x) :=
    ⟨Ioc 0 T,Ioc_mem_nhds hx.1 hx.2,hprod.1.aestronglyMeasurable⟩
  have hc := hcK.mul (intervalExtend_continuous T hT H).continuousAt
  have hd := (intervalIntegral.integral_hasDerivAt_right (hprod.mono_set hsub) hm hc).const_add y₀
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hx.1 hx.2] with t ht
  change H (projIcc 0 T hT t)=_
  rw [projIcc_of_mem hT ht]
  exact hH ⟨t,ht⟩

/-- A bounded integrable kernel has an actual differentiable Volterra solution
on a short interval, even if the kernel oscillates at the endpoint. -/
theorem volterra_differential_exists (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (hcK : ContinuousOn K (Ioo (0:ℝ) T))
    (y₀ : A) (M : ℝ) (hM : 0≤M) (hbound : ∀ s∈Icc (0:ℝ) T,‖K s‖≤M)
    (hsmall : T*M<1) :
    ∃ H : ℝ → A,Continuous H ∧ H 0=y₀ ∧
      ∀ x∈Ioo (0:ℝ) T,HasDerivAt H (K x*H x) x := by
  obtain ⟨H,hH⟩ := volterra_exists_small T hT K hK y₀ M hM hbound hsmall
  refine ⟨intervalExtend T hT H,intervalExtend_continuous T hT H,
    volterra_solution_initial T hT K y₀ H hH,?_⟩
  intro x hx
  exact volterra_solution_deriv T hT K hK y₀ H hH x hx
    ((hcK x hx).continuousAt (isOpen_Ioo.mem_nhds hx))

end AMSPhysical

#print axioms AMSPhysical.volterra_exists_small
