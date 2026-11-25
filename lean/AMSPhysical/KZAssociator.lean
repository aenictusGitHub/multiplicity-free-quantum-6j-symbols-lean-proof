import KZCanonical

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

theorem zero_normalized_skew_on (T : ℝ) (hT : 0<T) (a : ℝ → A) (D R : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) T,star (a x)= -a x)
    (hD : ∀ x∈Ioo (0:ℝ) T,HasDerivAt D (a x*D x) x)
    (hR : ∀ x∈Ioo (0:ℝ) T,R x∈unitary A)
    (h₀ : Tendsto (fun t => D t*R t) (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) T) : D x=0 := by
  have hlim : Tendsto (fun t => ‖star (D t*R t)*(D t*R t)‖)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (h₀.star.mul h₀).norm
  have he : (fun t => ‖star (D t*R t)*(D t*R t)‖)=ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun _ => ‖star (D x)*D x‖) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    have hstar : star (D t*R t)*(D t*R t)=star (R t)*(star (D t)*D t)*R t := by
      simp only [star_mul,mul_assoc]
    rw [hstar,CStarRing.norm_mul_mem_unitary _ (hR t ht),
      CStarRing.norm_mem_unitary_mul _ (unitary.star_mem (hR t ht)),
      skew_ode_gram_constant_on T a D ha hD t x ht hx]
  have hz : ‖star (D x)*D x‖=0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' he)
  exact (CStarRing.star_mul_self_eq_zero_iff _).mp (norm_eq_zero.mp hz)

theorem normalized_skew_unique_on (T : ℝ) (hT : 0<T) (a : ℝ → A) (G H R : ℝ → A)
    (ha : ∀ x∈Ioo (0:ℝ) T,star (a x)= -a x)
    (hG : ∀ x∈Ioo (0:ℝ) T,HasDerivAt G (a x*G x) x)
    (hH : ∀ x∈Ioo (0:ℝ) T,HasDerivAt H (a x*H x) x)
    (hR : ∀ x∈Ioo (0:ℝ) T,R x∈unitary A)
    (h₀G : Tendsto (fun t => G t*R t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (h₀H : Tendsto (fun t => H t*R t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (x : ℝ) (hx : x∈Ioo (0:ℝ) T) : G x=H x := by
  apply sub_eq_zero.mp
  apply zero_normalized_skew_on T hT a (fun t => G t-H t) R ha _ hR _ x hx
  · intro t ht
    simpa only [mul_sub] using (hG t ht).sub (hH t ht)
  · simpa only [sub_mul,sub_self] using h₀G.sub h₀H

def leftKZ (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) : ℝ → CStarMatrix (Fin n) (Fin n) ℂ :=
  (matrix_kz_normalized_exists n a b ha hb).choose

theorem leftKZ_deriv (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (t : ℝ) (ht : t∈Ioo (0:ℝ) (3/4)) :
    HasDerivAt (leftKZ n a b ha hb) (realKZCoefficient a b t*leftKZ n a b ha hb t) t :=
  (matrix_kz_normalized_exists n a b ha hb).choose_spec.1 t ht

theorem leftKZ_normalized (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) :
    Tendsto (fun t => leftKZ n a b ha hb t*endpointPower a t)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
  (matrix_kz_normalized_exists n a b ha hb).choose_spec.2.1

theorem leftKZ_unitary (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (t : ℝ) (ht : t∈Ioo (0:ℝ) (3/4)) :
    leftKZ n a b ha hb t∈unitary (CStarMatrix (Fin n) (Fin n) ℂ) :=
  (matrix_kz_normalized_exists n a b ha hb).choose_spec.2.2 t ht

theorem leftKZ_unique (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (G : ℝ → CStarMatrix (Fin n) (Fin n) ℂ)
    (hG : ∀ t∈Ioo (0:ℝ) (3/4),HasDerivAt G (realKZCoefficient a b t*G t) t)
    (h₀G : Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) (3/4)) : G t=leftKZ n a b ha hb t :=
  normalized_skew_unique_on (3/4) (by norm_num) (realKZCoefficient a b) G
    (leftKZ n a b ha hb) (endpointPower a)
    (fun x _ => realKZCoefficient_skew a b ha hb x) hG (leftKZ_deriv n a b ha hb)
    (fun x _ => endpointPower_unitary a ha x) h₀G (leftKZ_normalized n a b ha hb) t ht

def rightKZ (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (t : ℝ) : CStarMatrix (Fin n) (Fin n) ℂ :=
  leftKZ n b a hb ha (1-t)

theorem reflected_kzCoefficient (a b : A) (t : ℝ) :
    (-1:ℝ) • realKZCoefficient b a (1-t)=realKZCoefficient a b t := by
  have h₁ : 1-t-1= -t := by ring
  have h₂ : 1-t= -(t-1) := by ring
  have e₁ : (1-t-1)⁻¹= -t⁻¹ := by rw [h₁,inv_neg]
  have e₂ : (1-t)⁻¹= -(t-1)⁻¹ := by rw [h₂,inv_neg]
  simp only [realKZCoefficient,e₁,e₂,smul_add,smul_smul]
  module

theorem rightKZ_deriv (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (t : ℝ) (ht : t∈Ioo (1/4:ℝ) 1) :
    HasDerivAt (rightKZ n a b ha hb) (realKZCoefficient a b t*rightKZ n a b ha hb t) t := by
  have hu : 1-t∈Ioo (0:ℝ) (3/4) := by constructor <;> linarith [ht.1,ht.2]
  have hd := (leftKZ_deriv n b a hb ha (1-t) hu).scomp t
    ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))
  simpa only [sub_zero,zero_sub,← smul_mul_assoc,reflected_kzCoefficient,rightKZ,
    Function.comp_def] using hd

/-- The canonical connection between the two independently constructed,
normalized endpoint solutions. No quantum 6j formula occurs in this definition. -/
def kzConnection (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) : unitary (CStarMatrix (Fin n) (Fin n) ℂ) :=
  star ⟨leftKZ n b a hb ha (1/2),leftKZ_unitary n b a hb ha (1/2) (by norm_num)⟩ *
    ⟨leftKZ n a b ha hb (1/2),leftKZ_unitary n a b ha hb (1/2) (by norm_num)⟩

theorem kzConnection_constant (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (t : ℝ) (ht : t∈Ioo (1/4:ℝ) (3/4)) :
    star (rightKZ n a b ha hb t)*leftKZ n a b ha hb t=(kzConnection n a b ha hb : CStarMatrix (Fin n) (Fin n) ℂ) := by
  have hd (x : ℝ) (hx : x∈Ioo (1/4:ℝ) (3/4)) :
      HasDerivAt (fun s => star (rightKZ n a b ha hb s)*leftKZ n a b ha hb s) 0 x := by
    have h₀ := leftKZ_deriv n a b ha hb x ⟨by linarith [hx.1],hx.2⟩
    have h₁ := rightKZ_deriv n a b ha hb x ⟨hx.1,by linarith [hx.2]⟩
    convert h₁.star.mul h₀ using 1
    rw [star_mul,realKZCoefficient_skew a b ha hb]
    noncomm_ring
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (1/4:ℝ) (3/4)).isPreconnected
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) ht (by norm_num : (1/2:ℝ)∈Ioo (1/4:ℝ) (3/4))
  change star (rightKZ n a b ha hb t)*leftKZ n a b ha hb t=
    star (leftKZ n b a hb ha (1/2))*leftKZ n a b ha hb (1/2)
  have hu : (1:ℝ)-1/2=1/2 := by norm_num
  simpa only [rightKZ,hu] using he

end AMSPhysical

#print axioms AMSPhysical.kzConnection
#print axioms AMSPhysical.kzConnection_constant
