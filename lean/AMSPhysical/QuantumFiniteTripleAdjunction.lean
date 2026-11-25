import QuantumFiniteTripleCreation
import QuantumFiniteTripleAnnihilation
import QuantumTripleMetricBalance
import WeightedShiftMetricAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem finiteTripleLeftAnnihilation_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) (u : quantumOccupationTripleSpace n (l+1) (m+1) c) :
    physicalTripleBilin q n (l+1) (m+1) c (finiteTripleLeftCreation q n l m c v) u=
      physicalTripleBilin q n l m c v (mixedAnnihilationScale q n l m • finiteTripleLeftAnnihilation q n l m c u) := by
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n (l+1) (m+1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  apply weightedShift_metric_adjoint (V:=V) (W:=W)
    (occupationTripleBasis n l m c) (occupationTripleBasis n (l+1) (m+1) c)
    (occupationTripleEmbedding n l m c) (occupationTripleEmbedding n (l+1) (m+1) c)
    (occupationTripleEmbedding_injective n l m c) (occupationTripleEmbedding_injective n (l+1) (m+1) c)
    (physicalTripleWeight q n l m c) (physicalTripleWeight q n (l+1) (m+1) c)
    (finiteTripleLeftCreation q n l m c) (finiteTripleLeftAnnihilation q n l m c)
    (tripleLeftCreationShift n) (tripleLeftCreationCoefficient q n) (tripleLeftAnnihilationCoefficient q n)
    (mixedAnnihilationScale q n l m)
  · intro p
    change occupationTripleCoefficients n (l+1) (m+1) c (finiteTripleLeftCreation q n l m c (occupationTripleBasis n l m c p))=_
    rw [occupationTripleCoefficients_leftCreation,occupationTripleCoefficients_basis]
    simp only [tripleLeftCreation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
  · intro p
    change occupationTripleCoefficients n l m c (finiteTripleLeftAnnihilation q n l m c (occupationTripleBasis n (l+1) (m+1) c p))=_
    rw [occupationTripleCoefficients_leftAnnihilation,occupationTripleCoefficients_basis]
    simp only [tripleLeftAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul,sub_eq_add_neg]
  · intro p z i hi
    have hx : z.1=shiftedOccupation n l 1 i p.1 := Subtype.ext (congrArg Prod.fst hi).symm
    have hy : z.2.1=shiftedOccupation n m 1 i p.2.1 := Subtype.ext (congrArg (fun w =>w.2.1) hi).symm
    have hz : z.2.2=p.2.2 := by
      apply Subtype.ext
      simpa only [occupationTripleEmbedding,tripleLeftCreationShift,Prod.snd_add,add_zero] using
        (congrArg (fun w =>w.2.2) hi).symm
    rw [hi.symm,show z=(shiftedOccupation n l 1 i p.1,shiftedOccupation n m 1 i p.2.1,p.2.2) from Prod.ext hx (Prod.ext hy hz)]
    exact tripleLeft_metric_balance q hq hq1 n l m c i p

theorem finiteTripleRightAnnihilation_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) (u : quantumOccupationTripleSpace n l (m+1) (c+1)) :
    physicalTripleBilin q n l (m+1) (c+1) (finiteTripleRightCreation q n l m c v) u=
      physicalTripleBilin q n l m c v (mixedAnnihilationScale q n m c • finiteTripleRightAnnihilation q n l m c u) := by
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n l (m+1) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  apply weightedShift_metric_adjoint (V:=V) (W:=W)
    (occupationTripleBasis n l m c) (occupationTripleBasis n l (m+1) (c+1))
    (occupationTripleEmbedding n l m c) (occupationTripleEmbedding n l (m+1) (c+1))
    (occupationTripleEmbedding_injective n l m c) (occupationTripleEmbedding_injective n l (m+1) (c+1))
    (physicalTripleWeight q n l m c) (physicalTripleWeight q n l (m+1) (c+1))
    (finiteTripleRightCreation q n l m c) (finiteTripleRightAnnihilation q n l m c)
    (tripleRightCreationShift n) (tripleRightCreationCoefficient q n) (tripleRightAnnihilationCoefficient q n)
    (mixedAnnihilationScale q n m c)
  · intro p
    change occupationTripleCoefficients n l (m+1) (c+1) (finiteTripleRightCreation q n l m c (occupationTripleBasis n l m c p))=_
    rw [occupationTripleCoefficients_rightCreation,occupationTripleCoefficients_basis]
    simp only [tripleRightCreation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
  · intro p
    change occupationTripleCoefficients n l m c (finiteTripleRightAnnihilation q n l m c (occupationTripleBasis n l (m+1) (c+1) p))=_
    rw [occupationTripleCoefficients_rightAnnihilation,occupationTripleCoefficients_basis]
    simp only [tripleRightAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul,sub_eq_add_neg]
  · intro p z i hi
    have hx : z.1=p.1 := by
      apply Subtype.ext
      simpa only [occupationTripleEmbedding,tripleRightCreationShift,Prod.fst_add,add_zero] using
        (congrArg Prod.fst hi).symm
    have hy : z.2.1=shiftedOccupation n m 1 i p.2.1 := Subtype.ext (congrArg (fun w =>w.2.1) hi).symm
    have hz : z.2.2=shiftedOccupation n c 1 i p.2.2 := Subtype.ext (congrArg (fun w =>w.2.2) hi).symm
    rw [hi.symm,show z=(p.1,shiftedOccupation n m 1 i p.2.1,shiftedOccupation n c 1 i p.2.2) from Prod.ext hx (Prod.ext hy hz)]
    exact tripleRight_metric_balance q hq hq1 n l m c i p

end AMSPhysical
#print axioms AMSPhysical.finiteTripleLeftAnnihilation_adjoint
#print axioms AMSPhysical.finiteTripleRightAnnihilation_adjoint
