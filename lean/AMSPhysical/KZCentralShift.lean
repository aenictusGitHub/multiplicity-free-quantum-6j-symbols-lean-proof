import KZNaturality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousStar A] [StarModule ℝ A] [CStarRing A] [CompleteSpace A]

def IsCentralResidue (c : A) : Prop := ∀ y : A,Commute c y

theorem residuePower_central (c : A) (hc : IsCentralResidue c) (t : ℝ) (y : A) :
    Commute (residuePower c t) y :=
  ((hc y).smul_left (Real.log t)).exp_left ℝ

theorem endpointPower_add_central (a c : A) (hc : IsCentralResidue c) (t : ℝ) :
    endpointPower (a+c) t=endpointPower a t*endpointPower c t := by
  unfold endpointPower
  rw [smul_add,NormedSpace.exp_add_of_commute
    (((hc a).symm.smul_left (-Real.log t)).smul_right (-Real.log t))]

theorem residuePower_reflected_deriv (d : A) (t : ℝ) (ht : t<1) :
    HasDerivAt (fun s => residuePower d (1-s))
      (((t-1)⁻¹ • d)*residuePower d (1-t)) t := by
  have hd := (residuePower_deriv d (1-t) (by linarith)).scomp t
    ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))
  convert hd using 1
  simp only [zero_sub,← smul_mul_assoc,smul_smul]
  have hi : -(1-t)⁻¹=(t-1)⁻¹ := by rw [← inv_neg]; congr 1; ring
  simp only [neg_one_mul,hi]

def centralGauge (c d : A) (t : ℝ) : A := residuePower c t*residuePower d (1-t)

theorem centralGauge_central (c d : A) (hc : IsCentralResidue c) (hd : IsCentralResidue d)
    (t : ℝ) (y : A) : Commute (centralGauge c d t) y :=
  (residuePower_central c hc t y).mul_left (residuePower_central d hd (1-t) y)

theorem centralGauge_deriv (c d : A) (hc : IsCentralResidue c) (t : ℝ)
    (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (centralGauge c d) (realKZCoefficient c d t*centralGauge c d t) t := by
  have hh := (residuePower_deriv c t ht.1).mul (residuePower_reflected_deriv d t ht.2)
  convert hh using 1
  dsimp [realKZCoefficient,centralGauge]
  rw [add_mul]
  have he := (residuePower_central c hc t ((t-1)⁻¹ • d)).eq
  calc
    (t⁻¹ • c)*(residuePower c t*residuePower d (1-t))+
        ((t-1)⁻¹ • d)*(residuePower c t*residuePower d (1-t)) =
      (t⁻¹ • c*residuePower c t)*residuePower d (1-t)+
        (((t-1)⁻¹ • d)*residuePower c t)*residuePower d (1-t) := by noncomm_ring
    _ = _ := by rw [← he]; noncomm_ring

theorem centralGauge_solution (a b c d : A) (hc : IsCentralResidue c) (hd : IsCentralResidue d)
    (G : ℝ → A) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hG : HasDerivAt G (realKZCoefficient a b t*G t) t) :
    HasDerivAt (fun s => centralGauge c d s*G s)
      (realKZCoefficient (a+c) (b+d) t*(centralGauge c d t*G t)) t := by
  have h := (centralGauge_deriv c d hc t ht).mul hG
  convert h using 1
  have he : realKZCoefficient (a+c) (b+d) t=
      realKZCoefficient a b t+realKZCoefficient c d t := by
    unfold realKZCoefficient
    module
  rw [he]
  have hcomm := (centralGauge_central c d hc hd t (realKZCoefficient a b t)).eq
  rw [add_mul,← mul_assoc,← hcomm]
  noncomm_ring

theorem centralGauge_normalizer_cancel (a c d : A) (hc : IsCentralResidue c)
    (G : A) (t : ℝ) :
    centralGauge c d t*G*endpointPower (a+c) t=
      residuePower d (1-t)*(G*endpointPower a t) := by
  rw [endpointPower_add_central a c hc]
  unfold centralGauge
  have h₁ := (residuePower_central c hc t (residuePower d (1-t))).eq
  have h₂ := (residuePower_central c hc t (G*endpointPower a t)).eq
  calc
    (residuePower c t*residuePower d (1-t))*G*(endpointPower a t*endpointPower c t)=
      residuePower d (1-t)*(residuePower c t*(G*endpointPower a t))*endpointPower c t := by
        rw [h₁]; noncomm_ring
    _=residuePower d (1-t)*((G*endpointPower a t)*residuePower c t)*endpointPower c t := by rw [h₂]
    _=_ := by simp only [mul_assoc,residuePower_inverse,mul_one]

theorem residuePower_reflected_limit (d : A) :
    Tendsto (fun t : ℝ => residuePower d (1-t)) (nhds 0) (nhds 1) := by
  have hsub : ContinuousAt (fun t : ℝ => 1-t) 0 := continuousAt_const.sub continuousAt_id
  have hl : ContinuousAt Real.log ((fun t : ℝ => 1-t) 0) := Real.continuousAt_log (by norm_num)
  have hlog : ContinuousAt (fun t : ℝ => Real.log (1-t)) 0 := hl.comp hsub
  have he : ContinuousAt (fun t : ℝ => residuePower d (1-t)) 0 :=
    NormedSpace.exp_continuous.continuousAt.comp (hlog.smul continuousAt_const)
  simpa [residuePower] using he.tendsto

theorem centralGauge_normalized (a c d : A) (hc : IsCentralResidue c) (G : ℝ → A)
    (hG : Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1)) :
    Tendsto (fun t => (centralGauge c d t*G t)*endpointPower (a+c) t)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  simp_rw [centralGauge_normalizer_cancel a c d hc]
  simpa using ((residuePower_reflected_limit d).mono_left nhdsWithin_le_nhds).mul hG

theorem skew_add (a c : A) (ha : star a= -a) (hc : star c= -c) : star (a+c)= -(a+c) := by
  simp only [star_add,ha,hc,neg_add]

theorem leftKZ_central_shift (n : ℕ) (a b c d : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (hc : star c= -c) (hd : star d= -d)
    (hcc : IsCentralResidue c) (hdd : IsCentralResidue d)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) (3/4)) :
    leftKZ n (a+c) (b+d) (skew_add a c ha hc) (skew_add b d hb hd) t=
      centralGauge c d t*leftKZ n a b ha hb t := by
  symm
  apply leftKZ_unique n (a+c) (b+d) (skew_add a c ha hc) (skew_add b d hb hd)
    (fun x => centralGauge c d x*leftKZ n a b ha hb x)
  · intro x hx
    exact centralGauge_solution a b c d hcc hdd _ x ⟨hx.1,by linarith [hx.2]⟩
      (leftKZ_deriv n a b ha hb x hx)
  · exact centralGauge_normalized a c d hcc _ (leftKZ_normalized n a b ha hb)
  · exact ht

theorem centralGauge_unitary (c d : A) (hc : star c= -c) (hd : star d= -d) (t : ℝ) :
    centralGauge c d t∈unitary A :=
  (unitary A).mul_mem (residuePower_unitary c hc t) (residuePower_unitary d hd (1-t))

theorem centralGauge_half_swap (c d : A) (hc : IsCentralResidue c) :
    centralGauge d c (1/2)=centralGauge c d (1/2) := by
  have he : (1:ℝ)-1/2=1/2 := by norm_num
  simp only [centralGauge,he]
  exact (residuePower_central c hc (1/2) (residuePower d (1/2))).eq.symm

/-- Adding central skew-adjoint residues leaves the actual KZ connection unchanged. -/
theorem kzConnection_central_shift (n : ℕ) (a b c d : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (hc : star c= -c) (hd : star d= -d)
    (hcc : IsCentralResidue c) (hdd : IsCentralResidue d) :
    (kzConnection n (a+c) (b+d) (skew_add a c ha hc) (skew_add b d hb hd) :
      CStarMatrix (Fin n) (Fin n) ℂ)=kzConnection n a b ha hb := by
  change star (leftKZ n (b+d) (a+c) (skew_add b d hb hd) (skew_add a c ha hc) (1/2))*
    leftKZ n (a+c) (b+d) (skew_add a c ha hc) (skew_add b d hb hd) (1/2)=
    star (leftKZ n b a hb ha (1/2))*leftKZ n a b ha hb (1/2)
  rw [leftKZ_central_shift n b a d c hb ha hd hc hdd hcc (1/2) (by norm_num),
    leftKZ_central_shift n a b c d ha hb hc hd hcc hdd (1/2) (by norm_num),
    centralGauge_half_swap c d hcc,star_mul]
  have hu : star (centralGauge c d (1/2))*centralGauge c d (1/2)=1 :=
    (unitary.mem_iff.mp (centralGauge_unitary c d hc hd (1/2))).1
  calc
    (star (leftKZ n b a hb ha (1/2))*star (centralGauge c d (1/2)))*
      (centralGauge c d (1/2)*leftKZ n a b ha hb (1/2))=
      star (leftKZ n b a hb ha (1/2))*
        (star (centralGauge c d (1/2))*centralGauge c d (1/2))*leftKZ n a b ha hb (1/2) := by noncomm_ring
    _=_ := by rw [hu,mul_one]

/-- The affine unitary covariance needed for the rank-reduction argument. -/
theorem kzConnection_affine_unitary (n : ℕ) (a b c d : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (hc : star c= -c) (hd : star d= -d)
    (hcc : IsCentralResidue c) (hdd : IsCentralResidue d)
    (S : unitary (CStarMatrix (Fin n) (Fin n) ℂ)) :
    (kzConnection n (unitaryConj S a+c) (unitaryConj S b+d)
      (skew_add _ c (unitaryConj_skew S a ha) hc)
      (skew_add _ d (unitaryConj_skew S b hb) hd) : CStarMatrix (Fin n) (Fin n) ℂ)=
      unitaryConj S (kzConnection n a b ha hb : CStarMatrix (Fin n) (Fin n) ℂ) := by
  rw [kzConnection_central_shift n (unitaryConj S a) (unitaryConj S b) c d
    (unitaryConj_skew S a ha) (unitaryConj_skew S b hb) hc hd hcc hdd]
  exact kzConnection_conj n a b ha hb S

end AMSPhysical

#print axioms AMSPhysical.leftKZ_central_shift
#print axioms AMSPhysical.kzConnection_affine_unitary
