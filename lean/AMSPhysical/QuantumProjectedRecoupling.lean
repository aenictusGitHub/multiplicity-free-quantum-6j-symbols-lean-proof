import QuantumFirstProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def rightPathWeightIndex (l m n : ℕ) (a : RightHighestPath l m n) : Fin (coupledLabel m n a.1+1) :=
  ⟨a.2.val,by have hh := channel_right_bound l (coupledLabel m n a.1) a.2;omega⟩

def projectedRightNorm (q : ℝ) (l m n : ℕ) (a : RightHighestPath l m n) : ℝ :=
  quantumWeight q (coupledLabel m n a.1) a.2.val/quantumHighestNorm q l (coupledLabel m n a.1) a.2

theorem firstTripleProjection_rightHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (a : RightHighestPath l m n) :
    firstTripleProjection l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)=
      (Real.sqrt (quantumHighestNorm q l (coupledLabel m n a.1) a.2))⁻¹ •
        unitaryQuantumClebschMap q hq hq1 m n a.1
          (standardWeightBasis (coupledLabel m n a.1) (rightPathWeightIndex l m n a)) := by
  unfold firstTripleProjection quantumRightTreeHighest quantumRightTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  rw [tensorFirstProjection_map_right
    (V:=RealQuantumSpace l) (W:=RealQuantumSpace (coupledLabel m n a.1))
    (U:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)]
  change unitaryQuantumClebschMap q hq hq1 m n a.1
    (finiteFirstProjection l (coupledLabel m n a.1)
      (unitaryQuantumClebschMap q hq hq1 l (coupledLabel m n a.1) a.2
        (standardWeightBasis (coupledLabel l (coupledLabel m n a.1) a.2) 0)))=_
  rw [unitaryClebsch_highest_firstProjection,map_smul]
  rfl

theorem projectedRightNorm_pos (q : ℝ) (hq : 0<q) (l m n : ℕ) (a : RightHighestPath l m n) :
    0<projectedRightNorm q l m n a :=
  div_pos (quantumWeight_pos q hq _ _) (quantumHighestNorm_pos q hq _ _ _)

theorem projectedRight_gram (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (a b : RightHighestPath l m n) :
    quantumTensorBilin q m n (firstTripleProjection l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2))
      (firstTripleProjection l m n (quantumRightTreeHighest q hq hq1 l m n b.1 b.2))=
      if a=b then projectedRightNorm q l m n a else 0 := by
  classical
  rw [firstTripleProjection_rightHighest,firstTripleProjection_rightHighest]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  rcases a with ⟨u,v⟩
  rcases b with ⟨u',v'⟩
  by_cases huu : u=u'
  · subst u'
    rw [unitaryQuantumClebschMap_isometry,quantumPair_basis]
    by_cases hvv : v=v'
    · subst v'
      rw [if_pos rfl,if_pos rfl]
      change (Real.sqrt (quantumHighestNorm q l (coupledLabel m n u) v))⁻¹*
        ((Real.sqrt (quantumHighestNorm q l (coupledLabel m n u) v))⁻¹*quantumWeight q (coupledLabel m n u) v.val)=
          quantumWeight q (coupledLabel m n u) v.val/quantumHighestNorm q l (coupledLabel m n u) v
      have hN := quantumHighestNorm_pos q hq l (coupledLabel m n u) v
      have hs := Real.sq_sqrt hN.le
      have hn := ne_of_gt (Real.sqrt_pos.mpr hN)
      field_simp
      rw [hs]
      ring
    · have hidx : rightPathWeightIndex l m n ⟨u,v⟩≠rightPathWeightIndex l m n ⟨u,v'⟩ := by
        intro he
        apply hvv
        apply Fin.ext
        have hh := congrArg (fun z : Fin (coupledLabel m n u+1) => z.val) he
        exact hh
      have hpath : (⟨u,v⟩ : RightHighestPath l m n)≠⟨u,v'⟩ :=
        fun he => hvv (eq_of_heq (Sigma.mk.inj he).2)
      rw [if_neg hidx,if_neg hpath,mul_zero,mul_zero]
  · have hpath : (⟨u,v⟩ : RightHighestPath l m n)≠⟨u',v'⟩ := fun he => huu (Sigma.mk.inj he).1
    rw [unitaryQuantumClebschMap_orthogonal q hq hq1 m n u u' huu,if_neg hpath,mul_zero,mul_zero]

theorem projectedRacah_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) :
    quantumRacahMatrix q hq hq1 l m n p a*projectedRightNorm q l m n a=
      quantumTensorBilin q m n
        (firstTripleProjection l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2))
        (firstTripleProjection l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)) := by
  have he := congrArg (fun v : RealQuantumTripleSpace l m n => quantumTensorBilin q m n
    (firstTripleProjection l m n v)
    (firstTripleProjection l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)))
    (quantumHighest_recoupling_identity q hq hq1 l m n p)
  dsimp only at he
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,projectedRight_gram,
    mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  exact he

/-- Reduction of the actual recoupling entry to one two-factor inner product. -/
theorem quantumRacah_projected_formula (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) :
    quantumRacahMatrix q hq hq1 l m n p a=
      Real.sqrt (quantumHighestNorm q l (coupledLabel m n a.1) a.2)/quantumWeight q (coupledLabel m n a.1) a.2.val*
        quantumTensorBilin q m n
          (firstTripleProjection l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2))
          (unitaryQuantumClebschMap q hq hq1 m n a.1
            (standardWeightBasis (coupledLabel m n a.1) (rightPathWeightIndex l m n a))) := by
  have he := projectedRacah_coefficient q hq hq1 l m n p a
  rw [firstTripleProjection_rightHighest,map_smul,smul_eq_mul] at he
  have hN := quantumHighestNorm_pos q hq l (coupledLabel m n a.1) a.2
  have hW := quantumWeight_pos q hq (coupledLabel m n a.1) a.2.val
  have hs := Real.sq_sqrt hN.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hN)
  have hratio : (Real.sqrt (quantumHighestNorm q l (coupledLabel m n a.1) a.2))⁻¹/
      projectedRightNorm q l m n a=
      Real.sqrt (quantumHighestNorm q l (coupledLabel m n a.1) a.2)/quantumWeight q (coupledLabel m n a.1) a.2.val := by
    unfold projectedRightNorm
    field_simp
    rw [hs]
  have hz := (eq_div_iff (ne_of_gt (projectedRightNorm_pos q hq l m n a))).mpr he
  calc
    _=_ := hz
    _=_ := by rw [← hratio];ring

end AMSPhysical

#print axioms AMSPhysical.quantumRacah_projected_formula
