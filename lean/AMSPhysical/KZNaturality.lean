import KZAssociator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousStar A] [StarModule ℝ A] [CStarRing A] [CompleteSpace A]

def unitaryConj (S : unitary A) (x : A) : A := (S:A)*x*star (S:A)

theorem unitaryConj_mul (S : unitary A) (x y : A) :
    unitaryConj S (x*y)=unitaryConj S x*unitaryConj S y := by
  have hs : star (S:A)*(S:A)=1 := (unitary.mem_iff.mp S.property).1
  unfold unitaryConj
  calc
    (S:A)*(x*y)*star (S:A)=(S:A)*x*(star (S:A)*(S:A))*y*star (S:A) := by rw [hs]; noncomm_ring
    _=_ := by noncomm_ring

theorem unitaryConj_one (S : unitary A) : unitaryConj S (1:A)=1 := by
  simp only [unitaryConj,mul_one]
  exact (unitary.mem_iff.mp S.property).2

theorem unitaryConj_skew (S : unitary A) (x : A) (hx : star x= -x) :
    star (unitaryConj S x)= -unitaryConj S x := by
  simp only [unitaryConj,star_mul,star_star,hx,mul_neg,neg_mul,mul_assoc]

theorem unitaryConj_exp (S : unitary A) (x : A) :
    NormedSpace.exp ℝ (unitaryConj S x)=unitaryConj S (NormedSpace.exp ℝ x) := by
  exact NormedSpace.exp_units_conj ℝ (unitary.toUnits S) x

theorem endpointPower_conj (S : unitary A) (a : A) (t : ℝ) :
    endpointPower (unitaryConj S a) t=unitaryConj S (endpointPower a t) := by
  unfold endpointPower
  have he : (-Real.log t) • unitaryConj S a=unitaryConj S ((-Real.log t) • a) := by
    simp only [unitaryConj,smul_mul_assoc,mul_smul_comm]
  rw [he,unitaryConj_exp]

theorem realKZCoefficient_conj (S : unitary A) (a b : A) (t : ℝ) :
    realKZCoefficient (unitaryConj S a) (unitaryConj S b) t=
      unitaryConj S (realKZCoefficient a b t) := by
  simp only [realKZCoefficient,unitaryConj,mul_add,add_mul,smul_mul_assoc,mul_smul_comm]

theorem unitaryConj_normalized (S : unitary A) (a : A) (G : ℝ → A)
    (hG : Tendsto (fun t => G t*endpointPower a t) (nhdsWithin 0 (Ioi 0)) (nhds 1)) :
    Tendsto (fun t => unitaryConj S (G t)*endpointPower (unitaryConj S a) t)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have he (t : ℝ) : unitaryConj S (G t)*endpointPower (unitaryConj S a) t=
      unitaryConj S (G t*endpointPower a t) := by
    rw [endpointPower_conj,unitaryConj_mul]
  simp_rw [he]
  have hS : Tendsto (fun _ : ℝ => (S:A)) (nhdsWithin 0 (Ioi 0)) (nhds (S:A)) := tendsto_const_nhds
  have h := (hS.mul hG).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => star (S:A)) (nhdsWithin 0 (Ioi 0)) (nhds (star (S:A))))
  have hs : (S:A)*star (S:A)=1 := (unitary.mem_iff.mp S.property).2
  simpa only [unitaryConj,mul_one,hs] using h

theorem leftKZ_conj (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b)
    (S : unitary (CStarMatrix (Fin n) (Fin n) ℂ)) (t : ℝ) (ht : t∈Ioo (0:ℝ) (3/4)) :
    leftKZ n (unitaryConj S a) (unitaryConj S b) (unitaryConj_skew S a ha)
      (unitaryConj_skew S b hb) t=unitaryConj S (leftKZ n a b ha hb t) := by
  symm
  apply leftKZ_unique n (unitaryConj S a) (unitaryConj S b)
    (unitaryConj_skew S a ha) (unitaryConj_skew S b hb)
    (fun x => unitaryConj S (leftKZ n a b ha hb x))
  · intro x hx
    have hd := ((leftKZ_deriv n a b ha hb x hx).const_mul
      (S:CStarMatrix (Fin n) (Fin n) ℂ)).mul_const (star (S:CStarMatrix (Fin n) (Fin n) ℂ))
    convert hd using 1
    rw [realKZCoefficient_conj,← unitaryConj_mul]
    rfl
  · exact unitaryConj_normalized S a _ (leftKZ_normalized n a b ha hb)
  · exact ht

/-- Naturality of the actual, independently constructed KZ connection.
The connection-intertwining equation is a conclusion, not a hypothesis. -/
theorem kzConnection_conj (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b)
    (S : unitary (CStarMatrix (Fin n) (Fin n) ℂ)) :
    (kzConnection n (unitaryConj S a) (unitaryConj S b) (unitaryConj_skew S a ha)
      (unitaryConj_skew S b hb) : CStarMatrix (Fin n) (Fin n) ℂ)=
      unitaryConj S (kzConnection n a b ha hb : CStarMatrix (Fin n) (Fin n) ℂ) := by
  change star (leftKZ n (unitaryConj S b) (unitaryConj S a)
      (unitaryConj_skew S b hb) (unitaryConj_skew S a ha) (1/2))*
    leftKZ n (unitaryConj S a) (unitaryConj S b)
      (unitaryConj_skew S a ha) (unitaryConj_skew S b hb) (1/2)=_
  rw [leftKZ_conj n b a hb ha S (1/2) (by norm_num),
    leftKZ_conj n a b ha hb S (1/2) (by norm_num)]
  change star (unitaryConj S (leftKZ n b a hb ha (1/2)))*
    unitaryConj S (leftKZ n a b ha hb (1/2))=
    unitaryConj S (star (leftKZ n b a hb ha (1/2))*leftKZ n a b ha hb (1/2))
  have hs : star (S:CStarMatrix (Fin n) (Fin n) ℂ)*(S:CStarMatrix (Fin n) (Fin n) ℂ)=1 :=
    (unitary.mem_iff.mp S.property).1
  simp only [unitaryConj,star_mul,star_star]
  calc
    ((S:CStarMatrix (Fin n) (Fin n) ℂ)*(star (leftKZ n b a hb ha (1/2))*star (S:CStarMatrix (Fin n) (Fin n) ℂ)))*
      ((S:CStarMatrix (Fin n) (Fin n) ℂ)*leftKZ n a b ha hb (1/2)*star (S:CStarMatrix (Fin n) (Fin n) ℂ))=
      (S:CStarMatrix (Fin n) (Fin n) ℂ)*star (leftKZ n b a hb ha (1/2))*
        (star (S:CStarMatrix (Fin n) (Fin n) ℂ)*(S:CStarMatrix (Fin n) (Fin n) ℂ))*
        leftKZ n a b ha hb (1/2)*star (S:CStarMatrix (Fin n) (Fin n) ℂ) := by noncomm_ring
    _=_ := by rw [hs]; noncomm_ring

end AMSPhysical

#print axioms AMSPhysical.kzConnection_conj
