import SearsCleared

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology
attribute [local fun_prop] qPochhammer_continuous

def searsBalancedF (Q a e : ℝ) (n : ℕ) (x : ℝ) : ℝ := a*x*Q^(1-(n:ℤ))/e

def searsBalancedLeft (Q a b d e : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (∑ k∈Finset.range (n+1),basic4Term Q a b (d*x/b) (Q^(-(n:ℤ))) d e (searsBalancedF Q a e n x) k)*
    qPochhammer Q e n*qPochhammer Q (searsBalancedF Q a e n x) n

def searsBalancedRight (Q a b d e : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j∈Finset.range (n+1),searsClearedTerm Q a b (d*x/b) d e (searsBalancedF Q a e n x) x n j

theorem sears_basic4_continuousAt (Q a b d e x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (n k : ℕ) (hk : k≤n) (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0)
    (hfP : qPochhammer Q (searsBalancedF Q a e n x) n≠0) :
    ContinuousAt (fun z => basic4Term Q a b (d*z/b) (Q^(-(n:ℤ))) d e (searsBalancedF Q a e n z) k) x := by
  have hQk := qPochhammer_ne_zero Q Q k (fun i _ => baseQ_factor_nonzero Q hQ hQ1 i)
  have hdk := qPochhammer_prefix_ne_zero Q d n k hdP hk
  have hek := qPochhammer_prefix_ne_zero Q e n k heP hk
  have hfk := qPochhammer_prefix_ne_zero Q _ n k hfP hk
  have hden : qPochhammer Q Q k*qPochhammer Q d k*qPochhammer Q e k*
      qPochhammer Q (searsBalancedF Q a e n x) k≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hQk hdk) hek) hfk
  unfold basic4Term
  apply ContinuousAt.div
  · fun_prop
  · unfold searsBalancedF
    fun_prop
  · exact hden

theorem searsBalancedLeft_continuousAt (Q a b d e x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (n : ℕ) (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0)
    (hfP : qPochhammer Q (searsBalancedF Q a e n x) n≠0) :
    ContinuousAt (searsBalancedLeft Q a b d e n) x := by
  have hs : ContinuousAt (fun z => ∑ k∈Finset.range (n+1),
      basic4Term Q a b (d*z/b) (Q^(-(n:ℤ))) d e (searsBalancedF Q a e n z) k) x := by
    apply tendsto_finset_sum
    intro k hk
    exact sears_basic4_continuousAt Q a b d e x hQ hQ1 n k
      (by have hh := Finset.mem_range.mp hk;omega) hdP heP hfP
  have hf : ContinuousAt (fun z => qPochhammer Q (searsBalancedF Q a e n z) n) x := by
    unfold searsBalancedF
    fun_prop
  exact (hs.mul continuousAt_const).mul hf

theorem searsBalancedRight_continuousAt (Q a b d e x : ℝ) (hb : b≠0) (hd : d≠0) (hx : x≠0)
    (n : ℕ) : ContinuousAt (searsBalancedRight Q a b d e n) x := by
  unfold searsBalancedRight
  apply tendsto_finset_sum
  intro j hj
  change ContinuousAt (fun z => searsClearedTerm Q a b (d*z/b) d e (searsBalancedF Q a e n z) z n j) x
  have hc : d*x/b≠0 := div_ne_zero (mul_ne_zero hd hx) hb
  unfold searsClearedTerm searsBalancedF
  fun_prop (disch := assumption)

theorem sears_generic_F_nonzero (Q a e x : ℝ) (hQ : Q≠0) (ha : a≠0) (he : e≠0)
    (n : ℕ) (h : SaalschutzGeneric Q (e/a) 1 x) :
    qPochhammer Q (searsBalancedF Q a e n x) n≠0 := by
  apply qPochhammer_ne_zero
  intro k hk hz
  have h₁ : (x/(e/a))*Q^(1-(n:ℤ)+(k:ℤ))=1 := by
    unfold searsBalancedF at hz
    rw [zpow_add₀ hQ,zpow_natCast]
    field_simp [he,ha] at hz ⊢
    linear_combination -hz
  have h₂ : x*Q^(1-(n:ℤ)+(k:ℤ))=(e/a)*Q^(0:ℤ) := by
    rw [zpow_zero,mul_one]
    field_simp [he,ha] at h₁ ⊢
    linear_combination h₁
  have hh := power_ratio_unique Q hQ x (e/a) (1-(n:ℤ)+(k:ℤ)) 0 h₂
  apply h.notScaledPower (0-(1-(n:ℤ)+(k:ℤ)))
  simpa only [mul_one] using hh

/-- Cleared terminating Sears transformation on its full admissible domain;
the extra generic-product restriction is removed by density and continuity. -/
theorem qSears_cleared_parametrized (Q a b d e x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (ha : a≠0) (hb : b≠0) (hd : d≠0) (he : e≠0) (hx : x≠0)
    (n : ℕ) (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0)
    (hfP : qPochhammer Q (searsBalancedF Q a e n x) n≠0) :
    searsBalancedLeft Q a b d e n x=searsBalancedRight Q a b d e n x := by
  let good : Set ℝ := {z | SaalschutzGeneric Q (e/a) 1 z}
  have hdense : Dense good := saalschutzGeneric_dense Q (e/a) 1
  letI : NeBot (𝓝[good] x) := mem_closure_iff_nhdsWithin_neBot.mp (hdense x)
  have hL := (searsBalancedLeft_continuousAt Q a b d e x hQ hQ1 n hdP heP hfP).tendsto.mono_left
    (show 𝓝[good] x≤𝓝 x from inf_le_left)
  have hR := (searsBalancedRight_continuousAt Q a b d e x hb hd hx n).tendsto.mono_left
    (show 𝓝[good] x≤𝓝 x from inf_le_left)
  have hEq : searsBalancedLeft Q a b d e n=ᶠ[𝓝[good] x]searsBalancedRight Q a b d e n := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzn := hz.ne_zero
    have hF : searsBalancedF Q a e n z≠0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero ha hzn) (zpow_ne_zero _ (ne_of_gt hQ))) he
    have hrel : d*z=b*(d*z/b) := by field_simp [hb]
    have hbal : e*searsBalancedF Q a e n z=a*z*Q^(1-(n:ℤ)) := by
      unfold searsBalancedF
      field_simp [he]
    exact qSears_cleared_generic Q a b (d*z/b) d e (searsBalancedF Q a e n z) z hQ hQ1
      ha hb (div_ne_zero (mul_ne_zero hd hzn) hb) hd he hF hzn hrel n hbal hdP heP
      (sears_generic_F_nonzero Q a e z (ne_of_gt hQ) ha he n hz)
      (qPochhammer_ne_zero Q z n (fun k _ => hz.C_factor (ne_of_gt hQ) k))
  exact tendsto_nhds_unique (Filter.Tendsto.congr' hEq hL) hR

theorem qSears_cleared (Q a b c d e f x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (ha : a≠0) (hb : b≠0) (hd : d≠0) (he : e≠0) (hx : x≠0)
    (hrel : d*x=b*c) (n : ℕ) (hbal : e*f=a*x*Q^(1-(n:ℤ)))
    (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0) (hfP : qPochhammer Q f n≠0) :
    (∑ k∈Finset.range (n+1),basic4Term Q a b c (Q^(-(n:ℤ))) d e f k)*
      qPochhammer Q e n*qPochhammer Q f n=
      ∑ j∈Finset.range (n+1),searsClearedTerm Q a b c d e f x n j := by
  have hc : c=d*x/b := by apply (eq_div_iff hb).mpr;linear_combination -hrel
  have hf : f=searsBalancedF Q a e n x := by
    unfold searsBalancedF
    apply (eq_div_iff he).mpr
    linear_combination hbal
  subst c
  subst f
  exact qSears_cleared_parametrized Q a b d e x hQ hQ1 ha hb hd he hx n hdP heP hfP

end AMSPhysical

#print axioms AMSPhysical.qSears_cleared
