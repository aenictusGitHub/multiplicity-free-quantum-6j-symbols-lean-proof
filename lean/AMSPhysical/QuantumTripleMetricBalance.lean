import QuantumPhysicalTripleMetric
import QuantumMixedAnnihilationBalance
import QuantumTripleAnnihilation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLeft_metric_balance (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (i : Fin (n+1)) (p : OccupationTripleIndex n l m c) :
    tripleLeftCreationCoefficient q n i (occupationTripleEmbedding n l m c p)*
      physicalTripleWeight q n (l+1) (m+1) c
        (shiftedOccupation n l 1 i p.1,shiftedOccupation n m 1 i p.2.1,p.2.2)=
      mixedAnnihilationScale q n l m*
        tripleLeftAnnihilationCoefficient q n i (occupationTripleEmbedding n l m c p+tripleLeftCreationShift n i)*
          physicalTripleWeight q n l m c p := by
  have h0:=mixedAnnihilation_coefficient_balance q hq hq1 n l m i p.1 p.2.1
  unfold physicalTripleWeight tripleLeftCreationCoefficient tripleLeftAnnihilationCoefficient occupationTripleEmbedding
  simp only [tripleLeftCreationShift,Prod.fst_add,Prod.snd_add]
  change mixedCreationCoefficient q n i (p.1.val,p.2.1.val)*
      (occupationCompactWeight q n (l+1) (shiftedOccupation n l 1 i p.1)*
        occupationOppositeWeight q n (m+1) (shiftedOccupation n m 1 i p.2.1)*occupationCompactWeight q n c p.2.2)=_
  simp only [mixedCreationShift,Prod.mk_add_mk] at h0
  linear_combination (occupationCompactWeight q n c p.2.2)*h0

theorem tripleRight_metric_balance (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (i : Fin (n+1)) (p : OccupationTripleIndex n l m c) :
    tripleRightCreationCoefficient q n i (occupationTripleEmbedding n l m c p)*
      physicalTripleWeight q n l (m+1) (c+1)
        (p.1,shiftedOccupation n m 1 i p.2.1,shiftedOccupation n c 1 i p.2.2)=
      mixedAnnihilationScale q n m c*
        tripleRightAnnihilationCoefficient q n i (occupationTripleEmbedding n l m c p+tripleRightCreationShift n i)*
          physicalTripleWeight q n l m c p := by
  have h0:=mixedAnnihilation_coefficient_balance q hq hq1 n m c i.rev
    (occupationReflection n m p.2.1) (occupationReflection n c p.2.2)
  rw [← occupationReflection_unit_shift n m i p.2.1,← occupationReflection_unit_shift n c i p.2.2,
    occupationReflection_compact_weight q (ne_of_gt hq),occupationReflection_opposite_weight q (ne_of_gt hq),
    occupationReflection_compact_weight q (ne_of_gt hq),occupationReflection_opposite_weight q (ne_of_gt hq)] at h0
  unfold physicalTripleWeight tripleRightCreationCoefficient tripleRightAnnihilationCoefficient occupationTripleEmbedding
  simp only [tripleRightCreationShift,Prod.fst_add,Prod.snd_add,occupationLatticeReflect_add,occupationLatticeReflect_single]
  change mixedCreationCoefficient q n i.rev (occupationLatticeReflect n p.2.1.val,occupationLatticeReflect n p.2.2.val)*
      (occupationCompactWeight q n l p.1*occupationOppositeWeight q n (m+1) (shiftedOccupation n m 1 i p.2.1)*
        occupationCompactWeight q n (c+1) (shiftedOccupation n c 1 i p.2.2))=_
  change mixedCreationCoefficient q n i.rev (occupationLatticeReflect n p.2.1.val,occupationLatticeReflect n p.2.2.val)*
      (occupationOppositeWeight q n (m+1) (shiftedOccupation n m 1 i p.2.1)*
        occupationCompactWeight q n (c+1) (shiftedOccupation n c 1 i p.2.2))=
      mixedAnnihilationScale q n m c*mixedAnnihilationCoefficient q n i.rev
        ((occupationLatticeReflect n p.2.1.val,occupationLatticeReflect n p.2.2.val)+mixedCreationShift n i.rev)*
        (occupationOppositeWeight q n m p.2.1*occupationCompactWeight q n c p.2.2) at h0
  simp only [mixedCreationShift,Prod.mk_add_mk] at h0
  linear_combination (occupationCompactWeight q n l p.1)*h0

end AMSPhysical
