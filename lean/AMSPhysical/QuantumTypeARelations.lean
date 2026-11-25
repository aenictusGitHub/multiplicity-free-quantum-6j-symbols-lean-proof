import QuantumTypeAWeights
import QuantumSerreSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]
local notation "U" => typeAAlgebraGenerator

theorem uqA_inverse (q : K) (n : ℕ) (i : Fin n) : U q n i 2*U q n i 3=1 := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_one] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.inverse (q:=q) i)

theorem uqA_inverse' (q : K) (n : ℕ) (i : Fin n) : U q n i 3*U q n i 2=1 := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_one] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.inverse' (q:=q) i)

theorem uqA_torus (q : K) (n : ℕ) (i j : Fin n) : U q n i 2*U q n j 2=U q n j 2*U q n i 2 := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.torus (q:=q) i j)

theorem uqA_weightE (q : K) (n : ℕ) (i j : Fin n) :
    U q n i 2*U q n j 0=q^(typeACartan n i j) • (U q n j 0*U q n i 2) := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_smul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.weightE (q:=q) i j)

theorem uqA_weightF (q : K) (n : ℕ) (i j : Fin n) :
    U q n i 2*U q n j 1=q^(-typeACartan n i j) • (U q n j 1*U q n i 2) := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_smul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.weightF (q:=q) i j)

theorem uqA_commutator (q : K) (n : ℕ) (i : Fin n) :
    U q n i 0*U q n i 1-U q n i 1*U q n i 0=(q-q⁻¹)⁻¹ • (U q n i 2-U q n i 3) := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_sub,map_smul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.commutator (q:=q) i)

theorem uqA_differentEF (q : K) (n : ℕ) (i j : Fin n) (hij : i≠j) :
    U q n i 0*U q n j 1=U q n j 1*U q n i 0 := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.differentEF (q:=q) i j hij)

theorem uqA_distantE (q : K) (n : ℕ) (i j : Fin n) (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    U q n i 0*U q n j 0=U q n j 0*U q n i 0 := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.distantE (q:=q) i j hd)

theorem uqA_distantF (q : K) (n : ℕ) (i j : Fin n) (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    U q n i 1*U q n j 1=U q n j 1*U q n i 1 := by
  simpa only [typeAAlgebraGenerator,typeAFreeGenerator,map_mul] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.distantF (q:=q) i j hd)

theorem uqA_serreELeft (q : K) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (U q n i 0) (U q n j 0)=0 := by
  simpa only [serrePolynomial,typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_sub,map_add,map_smul,map_zero] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.serreELeft (q:=q) i j hij)

theorem uqA_serreERight (q : K) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (U q n j 0) (U q n i 0)=0 := by
  simpa only [serrePolynomial,typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_sub,map_add,map_smul,map_zero] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.serreERight (q:=q) i j hij)

theorem uqA_serreFLeft (q : K) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (U q n i 1) (U q n j 1)=0 := by
  simpa only [serrePolynomial,typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_sub,map_add,map_smul,map_zero] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.serreFLeft (q:=q) i j hij)

theorem uqA_serreFRight (q : K) (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    serrePolynomial q (U q n j 1) (U q n i 1)=0 := by
  simpa only [serrePolynomial,typeAAlgebraGenerator,typeAFreeGenerator,map_mul,map_sub,map_add,map_smul,map_zero] using
    RingQuot.mkAlgHom_rel K (QuantumTypeARelation.serreFRight (q:=q) i j hij)

theorem typeACartan_symmetric (n : ℕ) (i j : Fin n) : typeACartan n i j=typeACartan n j i := by
  unfold typeACartan
  by_cases hij : i=j
  · subst j
    simp
  · simp only [if_neg hij,if_neg (Ne.symm hij),or_comm]

theorem typeACartan_self (n : ℕ) (i : Fin n) : typeACartan n i i=2 := by simp [typeACartan]

theorem typeACartan_adjacent (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) : typeACartan n i j= -1 := by
  have hn : i≠j := by intro h;have hh := congrArg Fin.val h;omega
  simp only [typeACartan,if_neg hn,if_pos (Or.inl hij)]

theorem typeACartan_distant (n : ℕ) (i j : Fin n) (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    typeACartan n i j=0 := by
  unfold typeACartan
  split_ifs with h₁ h₂
  · have hh := congrArg Fin.val h₁
    omega
  · omega
  · rfl

theorem commute_inverse_right {A : Type*} [Ring A] (X Y Yi : A) (hY : Yi*Y=1) (hY' : Y*Yi=1)
    (hXY : X*Y=Y*X) : X*Yi=Yi*X := by
  calc
    _ = (Yi*Y)*X*Yi := by rw [hY,one_mul]
    _ = Yi*(Y*X)*Yi := by noncomm_ring
    _ = Yi*(X*Y)*Yi := by rw [hXY]
    _ = Yi*X*(Y*Yi) := by noncomm_ring
    _ = Yi*X := by rw [hY',mul_one]

theorem uqA_torus_inverse_right (q : K) (n : ℕ) (i j : Fin n) : U q n i 2*U q n j 3=U q n j 3*U q n i 2 :=
  commute_inverse_right _ _ _ (uqA_inverse' q n j) (uqA_inverse q n j) (uqA_torus q n i j)

theorem uqA_torus_inverses (q : K) (n : ℕ) (i j : Fin n) : U q n i 3*U q n j 3=U q n j 3*U q n i 3 :=
  commute_inverse_right _ _ _ (uqA_inverse' q n j) (uqA_inverse q n j) (uqA_torus_inverse_right q n j i).symm

theorem uqA_E_Kinv (q : K) (n : ℕ) (i j : Fin n) :
    U q n j 0*U q n i 3=q^(typeACartan n i j) • (U q n i 3*U q n j 0) := by
  calc
    _ = (U q n i 3*U q n i 2)*U q n j 0*U q n i 3 := by rw [uqA_inverse',one_mul]
    _ = U q n i 3*(U q n i 2*U q n j 0)*U q n i 3 := by noncomm_ring
    _ = _ := by
      rw [uqA_weightE]
      simp only [smul_mul_assoc,mul_smul_comm,mul_assoc,uqA_inverse,mul_one]

theorem uqA_F_Kinv (q : K) (n : ℕ) (i j : Fin n) :
    U q n j 1*U q n i 3=q^(-typeACartan n i j) • (U q n i 3*U q n j 1) := by
  calc
    _ = (U q n i 3*U q n i 2)*U q n j 1*U q n i 3 := by rw [uqA_inverse',one_mul]
    _ = U q n i 3*(U q n i 2*U q n j 1)*U q n i 3 := by noncomm_ring
    _ = _ := by
      rw [uqA_weightF]
      simp only [smul_mul_assoc,mul_smul_comm,mul_assoc,uqA_inverse,mul_one]

end AMSPhysical

#print axioms AMSPhysical.uqA_E_Kinv
#print axioms AMSPhysical.uqA_serreELeft
