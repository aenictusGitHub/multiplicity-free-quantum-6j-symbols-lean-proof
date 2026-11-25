import ComplexPhysicalAnalytic
import AMSClassicalPhysicalValue

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open Filter
open scoped Topology

/-- The independently constructed finite complex CG overlap at one is the
actual physical deformation limit. No AMS expression occurs in this identity. -/
theorem complexPhysicalTypeIWigner_at_one_actual_limit (h l m c:ℕ) (hadm:m≤l+c)
    (s t:QuantumCupIndex l m c):
    complexPhysicalTypeIWigner 1 h l m c s t=(physicalTypeIClassicalLimit h l m c hadm s t:ℂ):=by
  have hc:ContinuousAt (fun z:ℂ=>complexPhysicalTypeIWigner z h l m c s t) 1:=
    (complexPhysicalTypeIWigner_analyticAt_positive 1 (by norm_num) h l m c s t).continuousAt
  have hC:Tendsto (fun q:ℝ=>complexPhysicalTypeIWigner (q:ℂ) h l m c s t) (𝓝[≠] (1:ℝ))
      (𝓝 (complexPhysicalTypeIWigner 1 h l m c s t)):=
    hc.tendsto.comp ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hR:Tendsto (fun q:ℝ=>(physicalTypeIWignerFunction h l m c hadm s t q:ℂ)) (𝓝[≠] (1:ℝ))
      (𝓝 (physicalTypeIClassicalLimit h l m c hadm s t:ℂ)):=by
    rw [physicalTypeI_classical_AMS]
    exact (Complex.continuous_ofReal.tendsto _).comp (physicalTypeI_AMS_q_one_limit h l m c hadm s t)
  have he:(fun q:ℝ=>complexPhysicalTypeIWigner (q:ℂ) h l m c s t)=ᶠ[𝓝[≠] (1:ℝ)]
      (fun q:ℝ=>(physicalTypeIWignerFunction h l m c hadm s t q:ℂ)):=by
    have hp:∀ᶠ q:ℝ in 𝓝[≠] (1:ℝ),0<q:=
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hp,self_mem_nhdsWithin] with q hq hq1
    rw [physicalTypeIWignerFunction,dif_pos ⟨hq,hq1⟩]
    exact complexPhysicalTypeIWigner_ofReal_actual q hq hq1 h l m c hadm s t
  exact tendsto_nhds_unique (hC.congr' he) hR

theorem complexPhysicalTypeIIWigner_at_one_actual_limit (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    complexPhysicalTypeIIWigner 1 h a b c d hbal r t=(physicalTypeIIClassicalLimit h a b c d hbal r t:ℂ):=by
  have hc:ContinuousAt (fun z:ℂ=>complexPhysicalTypeIIWigner z h a b c d hbal r t) 1:=
    (complexPhysicalTypeIIWigner_analyticAt_positive 1 (by norm_num) h a b c d hbal r t).continuousAt
  have hC:Tendsto (fun q:ℝ=>complexPhysicalTypeIIWigner (q:ℂ) h a b c d hbal r t) (𝓝[≠] (1:ℝ))
      (𝓝 (complexPhysicalTypeIIWigner 1 h a b c d hbal r t)):=
    hc.tendsto.comp ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hR:Tendsto (fun q:ℝ=>(physicalTypeIIWignerFunction h a b c d hbal r t q:ℂ)) (𝓝[≠] (1:ℝ))
      (𝓝 (physicalTypeIIClassicalLimit h a b c d hbal r t:ℂ)):=by
    rw [physicalTypeII_classical_AMS]
    exact (Complex.continuous_ofReal.tendsto _).comp (physicalTypeII_AMS_q_one_limit h a b c d hbal r t)
  have he:(fun q:ℝ=>complexPhysicalTypeIIWigner (q:ℂ) h a b c d hbal r t)=ᶠ[𝓝[≠] (1:ℝ)]
      (fun q:ℝ=>(physicalTypeIIWignerFunction h a b c d hbal r t q:ℂ)):=by
    have hp:∀ᶠ q:ℝ in 𝓝[≠] (1:ℝ),0<q:=
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hp,self_mem_nhdsWithin] with q hq hq1
    rw [physicalTypeIIWignerFunction,dif_pos ⟨hq,hq1⟩]
    exact complexPhysicalTypeIIWigner_ofReal_actual q hq hq1 h a b c d hbal r t
  exact tendsto_nhds_unique (hC.congr' he) hR

end AMSPhysical
#print axioms AMSPhysical.complexPhysicalTypeIIWigner_at_one_actual_limit
