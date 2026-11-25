import OccupationTripleBasisProperties
import QuantumOccupationShifts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def finiteTripleLeftCreation (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n l m c →ₗ[ℝ] quantumOccupationTripleSpace n (l+1) (m+1) c :=
  (occupationTripleBasis n l m c).constr ℝ (fun p =>∑ i : Fin (n+1),
    tripleLeftCreationCoefficient q n i (occupationTripleEmbedding n l m c p) •
      occupationTripleBasis n (l+1) (m+1) c
        (shiftedOccupation n l 1 i p.1,shiftedOccupation n m 1 i p.2.1,p.2.2))

theorem finiteTripleLeftCreation_basis (q : ℝ) (n l m c : ℕ) (p : OccupationTripleIndex n l m c) :
    finiteTripleLeftCreation q n l m c (occupationTripleBasis n l m c p)=∑ i : Fin (n+1),
      tripleLeftCreationCoefficient q n i (occupationTripleEmbedding n l m c p) •
        occupationTripleBasis n (l+1) (m+1) c
          (shiftedOccupation n l 1 i p.1,shiftedOccupation n m 1 i p.2.1,p.2.2) :=
  Module.Basis.constr_basis _ _ _ _

theorem occupationTripleCoefficients_leftCreation (q : ℝ) (n l m c : ℕ) (v : quantumOccupationTripleSpace n l m c) :
    occupationTripleCoefficients n (l+1) (m+1) c (finiteTripleLeftCreation q n l m c v)=
      tripleLeftCreation q n (occupationTripleCoefficients n l m c v) := by
  have hMaps : (occupationTripleCoefficients n (l+1) (m+1) c).comp (finiteTripleLeftCreation q n l m c)=
      (tripleLeftCreation q n).comp (occupationTripleCoefficients n l m c) := by
    apply (occupationTripleBasis n l m c).ext
    intro p
    simp only [LinearMap.comp_apply,finiteTripleLeftCreation_basis,map_sum,map_smul,
      occupationTripleCoefficients_basis,tripleLeftCreation,LinearMap.sum_apply,weightedTranslation_single,
      one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]
    simp only [occupationTripleEmbedding,shiftedOccupation,tripleLeftCreationShift,Prod.fst_add,Prod.snd_add,Prod.mk_add_mk,add_zero,Nat.cast_one]
  exact DFunLike.congr_fun hMaps v

def finiteTripleRightCreation (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n l m c →ₗ[ℝ] quantumOccupationTripleSpace n l (m+1) (c+1) :=
  (occupationTripleBasis n l m c).constr ℝ (fun p =>∑ i : Fin (n+1),
    tripleRightCreationCoefficient q n i (occupationTripleEmbedding n l m c p) •
      occupationTripleBasis n l (m+1) (c+1)
        (p.1,shiftedOccupation n m 1 i p.2.1,shiftedOccupation n c 1 i p.2.2))

theorem finiteTripleRightCreation_basis (q : ℝ) (n l m c : ℕ) (p : OccupationTripleIndex n l m c) :
    finiteTripleRightCreation q n l m c (occupationTripleBasis n l m c p)=∑ i : Fin (n+1),
      tripleRightCreationCoefficient q n i (occupationTripleEmbedding n l m c p) •
        occupationTripleBasis n l (m+1) (c+1)
          (p.1,shiftedOccupation n m 1 i p.2.1,shiftedOccupation n c 1 i p.2.2) :=
  Module.Basis.constr_basis _ _ _ _

theorem occupationTripleCoefficients_rightCreation (q : ℝ) (n l m c : ℕ) (v : quantumOccupationTripleSpace n l m c) :
    occupationTripleCoefficients n l (m+1) (c+1) (finiteTripleRightCreation q n l m c v)=
      tripleRightCreation q n (occupationTripleCoefficients n l m c v) := by
  have hMaps : (occupationTripleCoefficients n l (m+1) (c+1)).comp (finiteTripleRightCreation q n l m c)=
      (tripleRightCreation q n).comp (occupationTripleCoefficients n l m c) := by
    apply (occupationTripleBasis n l m c).ext
    intro p
    simp only [LinearMap.comp_apply,finiteTripleRightCreation_basis,map_sum,map_smul,
      occupationTripleCoefficients_basis,tripleRightCreation,LinearMap.sum_apply,weightedTranslation_single,
      one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]
    simp only [occupationTripleEmbedding,shiftedOccupation,tripleRightCreationShift,Prod.fst_add,Prod.snd_add,Prod.mk_add_mk,add_zero,Nat.cast_one]
  exact DFunLike.congr_fun hMaps v

end AMSPhysical
