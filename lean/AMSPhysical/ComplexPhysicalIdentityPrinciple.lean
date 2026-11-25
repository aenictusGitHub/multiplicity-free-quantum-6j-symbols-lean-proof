import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology

/-- Positive-real physical agreement determines the full connected
holomorphic branch. The accumulating sequence is constructed explicitly. -/
theorem complexAnalytic_eqOn_of_positive_real (f g:ℂ → ℂ) (U:Set ℂ)
    (hU:IsOpen U) (hconn:IsPreconnected U) (h2:(2:ℂ)∈U)
    (hf:AnalyticOnNhd ℂ f U) (hg:AnalyticOnNhd ℂ g U)
    (hreal:∀ q:ℝ,0<q → q≠1 → (q:ℂ)∈U → f q=g q):Set.EqOn f g U:=by
  let s:ℕ → ℝ:=fun n=>2+(1/2:ℝ)^n
  have hs:Tendsto s atTop (𝓝 (2:ℝ)):=by
    have hp:Tendsto (fun n:ℕ=>(1/2:ℝ)^n) atTop (𝓝 (0:ℝ)):=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [add_zero] using tendsto_const_nhds.add hp
  have hsc:Tendsto (fun n:ℕ=>(s n:ℂ)) atTop (𝓝 (2:ℂ)):=
    (Complex.continuous_ofReal.tendsto 2).comp hs
  have hmem:∀ᶠ n:ℕ in atTop,(s n:ℂ)∈U:=hsc.eventually (hU.mem_nhds h2)
  have hcl:(2:ℂ)∈closure ({z:ℂ|f z=g z} \ {(2:ℂ)}):=by
    apply mem_closure_of_tendsto hsc
    filter_upwards [hmem] with n hn
    have hp:0<(1/2:ℝ)^n:=pow_pos (by norm_num) n
    have hpos:0<s n:=by dsimp only [s];linarith
    have hne:s n≠1:=by dsimp only [s];linarith
    have hne2:(s n:ℂ)≠2:=by
      intro he
      have hr:s n=2:=Complex.ofReal_injective (by simpa only [Complex.ofReal_ofNat] using he)
      dsimp only [s] at hr
      linarith
    exact ⟨hreal (s n) hpos hne hn,hne2⟩
  exact hf.eqOn_of_preconnected_of_mem_closure hg hconn h2 hcl

end AMSPhysical
#print axioms AMSPhysical.complexAnalytic_eqOn_of_positive_real
