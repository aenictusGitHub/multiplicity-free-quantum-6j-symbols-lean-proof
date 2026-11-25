import Volterra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Set Filter MeasureTheory intervalIntegral
open scoped Topology NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def scalarWeightMap (T c : ℝ) (H : C(Icc (0:ℝ) T,A)) : C(Icc (0:ℝ) T,A) where
  toFun t := Real.exp (c*t.val) • H t
  continuous_toFun := by fun_prop

def bieleckiStep (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (c : ℝ) (H : C(Icc (0:ℝ) T,A)) :
    C(Icc (0:ℝ) T,A) :=
  scalarWeightMap T (-c) (volterraStep T hT K hK y₀ (scalarWeightMap T c H))

theorem integral_real_exp_mul (c : ℝ) (hc : c≠0) (x : ℝ) :
    (∫ s in 0..x,Real.exp (c*s))=(Real.exp (c*x)-1)/c := by
  have hd (s : ℝ) : HasDerivAt (fun u => Real.exp (c*u)/c) (Real.exp (c*s)) s := by
    convert ((((hasDerivAt_id s).const_mul c).exp).div_const c) using 1
    field_simp
    rfl
  have hi : IntervalIntegrable (fun s => Real.exp (c*s)) volume 0 x :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (c*s))).intervalIntegrable 0 x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  simpa [sub_div] using he

theorem bieleckiStep_lipschitz (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (M c : ℝ) (hM : 0≤M) (hc : 0<c)
    (hbound : ∀ s∈Icc (0:ℝ) T,‖K s‖≤M) (H G : C(Icc (0:ℝ) T,A)) :
    ‖bieleckiStep T hT K hK y₀ c H-bieleckiStep T hT K hK y₀ c G‖≤(M/c)*‖H-G‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (div_nonneg hM hc.le) (norm_nonneg _))).mpr
  intro x
  have hsub : uIcc (0:ℝ) x.val⊆uIcc (0:ℝ) T := by
    rw [uIcc_of_le x.property.1,uIcc_of_le hT]
    exact Icc_subset_Icc_right x.property.2
  let W := scalarWeightMap T c H
  let Z := scalarWeightMap T c G
  have hW := (kernel_product_integrable T hT K hK W).mono_set hsub
  have hZ := (kernel_product_integrable T hT K hK Z).mono_set hsub
  have hmajor : IntervalIntegrable (fun s : ℝ => Real.exp (c*s)*(M*‖H-G‖)) volume 0 x.val :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (c*s)*(M*‖H-G‖))).intervalIntegrable 0 x.val
  have hpoint : ∀ s∈Ioc (0:ℝ) x.val,
      ‖K s*intervalExtend T hT W s-K s*intervalExtend T hT Z s‖≤
        Real.exp (c*s)*(M*‖H-G‖) := by
    intro s hs
    have hsT : s∈Icc (0:ℝ) T := ⟨hs.1.le,hs.2.trans x.property.2⟩
    have he : intervalExtend T hT W s-intervalExtend T hT Z s=
        Real.exp (c*s) • (intervalExtend T hT H s-intervalExtend T hT G s) := by
      simp only [intervalExtend,W,Z,scalarWeightMap,ContinuousMap.coe_mk,
        projIcc_of_mem hT hsT]
      rw [smul_sub]
    rw [← mul_sub,he]
    calc
      ‖K s*(Real.exp (c*s) • (intervalExtend T hT H s-intervalExtend T hT G s))‖≤
          ‖K s‖*(Real.exp (c*s)*‖intervalExtend T hT H s-intervalExtend T hT G s‖) := by
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
          norm_mul_le (K s) (Real.exp (c*s) • (intervalExtend T hT H s-intervalExtend T hT G s))
      _≤M*(Real.exp (c*s)*‖H-G‖) :=
        mul_le_mul (hbound s hsT)
          (mul_le_mul_of_nonneg_left
            (ContinuousMap.norm_coe_le_norm (H-G) (projIcc 0 T hT s)) (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hM
      _=Real.exp (c*s)*(M*‖H-G‖) := by ring
  have hn := intervalIntegral.norm_integral_le_of_norm_le x.property.1
    (Filter.Eventually.of_forall hpoint) hmajor
  have hexp : Real.exp (-c*x.val)*Real.exp (c*x.val)=1 := by
    rw [← Real.exp_add]
    have he : -c*x.val+c*x.val=0 := by ring
    rw [he,Real.exp_zero]
  have hfac : Real.exp (-c*x.val)*(Real.exp (c*x.val)-1)≤1 := by
    nlinarith [Real.exp_pos (-c*x.val)]
  change ‖Real.exp (-c*x.val) • (y₀+∫ s in 0..x.val,K s*intervalExtend T hT W s)-
    Real.exp (-c*x.val) • (y₀+∫ s in 0..x.val,K s*intervalExtend T hT Z s)‖≤_
  rw [← smul_sub,add_sub_add_left_eq_sub,← integral_sub hW hZ,norm_smul]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _≤Real.exp (-c*x.val)*(∫ s in 0..x.val,Real.exp (c*s)*(M*‖H-G‖)) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _=Real.exp (-c*x.val)*((Real.exp (c*x.val)-1)/c*(M*‖H-G‖)) := by
      rw [intervalIntegral.integral_mul_const,integral_real_exp_mul c (ne_of_gt hc)]
    _=((M/c)*‖H-G‖)*(Real.exp (-c*x.val)*(Real.exp (c*x.val)-1)) := by ring
    _≤(M/c)*‖H-G‖ := by
      exact (mul_le_mul_of_nonneg_left hfac
        (mul_nonneg (div_nonneg hM hc.le) (norm_nonneg _))).trans_eq (mul_one _)

/-- Global Volterra solvability on every compact interval, using the Bielecki
exponential weight to remove the small-interval restriction. -/
theorem volterra_exists (T : ℝ) (hT : 0≤T) (K : ℝ → A)
    (hK : IntervalIntegrable K volume 0 T) (y₀ : A) (M : ℝ) (hM : 0≤M)
    (hbound : ∀ s∈Icc (0:ℝ) T,‖K s‖≤M) :
    ∃ H : C(Icc (0:ℝ) T,A), ∀ t : Icc (0:ℝ) T,
      H t=y₀+∫ s in 0..t.val,K s*intervalExtend T hT H s := by
  let c := 2*M+1
  have hc : 0<c := by dsimp [c]; linarith
  let L : ℝ≥0 := ⟨M/c,div_nonneg hM hc.le⟩
  have hL : (L:ℝ)<1 := by
    change M/c<1
    apply (div_lt_iff₀ hc).mpr
    dsimp [c]
    linarith
  have hcon : ContractingWith L (bieleckiStep T hT K hK y₀ c) := by
    refine ⟨hL,?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro H G
    simpa only [dist_eq_norm] using bieleckiStep_lipschitz T hT K hK y₀ M c hM hc hbound H G
  let H := hcon.fixedPoint
  refine ⟨scalarWeightMap T c H,?_⟩
  intro t
  have he := congrArg (fun F : C(Icc (0:ℝ) T,A) => F t) hcon.fixedPoint_isFixedPt.eq
  change Real.exp (-c*t.val) •
    (y₀+∫ s in 0..t.val,K s*intervalExtend T hT (scalarWeightMap T c H) s)=H t at he
  change Real.exp (c*t.val) • H t=_
  rw [← he,smul_smul,← Real.exp_add]
  have hz : c*t.val+-c*t.val=0 := by ring
  rw [hz,Real.exp_zero,one_smul]

end AMSPhysical

#print axioms AMSPhysical.volterra_exists
