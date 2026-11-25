import QuantumTotalTripleRadial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

theorem occupationWeight_zero_coordinate (n : ℕ) (x : occupationWeights (Fin (n+1)) 0) (i : Fin (n+1)) :
    x.val i=0 := by
  have hlo:=x.property.1 i
  have hhi:=occupationWeight_bound 0 x i
  omega

theorem physicalTripleLeftRadialTotal_zero_first (q : ℝ) (n m c : ℕ) :
    physicalTripleLeftRadialTotal q n 0 m c=0 := by
  apply (occupationTripleBasis n 0 m c).ext
  intro p
  have hL : tripleLeftAnnihilation q n (Finsupp.single (occupationTripleEmbedding n 0 m c p) 1)=0 := by
    simp only [tripleLeftAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hz:=occupationWeight_zero_coordinate n p.1 i
    simp only [tripleLeftAnnihilationCoefficient,mixedAnnihilationCoefficient,occupationTripleEmbedding] at *
    rw [hz,qInteger_zero]
    simp only [mul_zero,zero_mul,Finsupp.single_zero]
  change occupationTripleSynthesis n 0 m c
    (tripleLeftCreation q n (tripleLeftAnnihilation q n
      (occupationTripleCoefficients n 0 m c (occupationTripleBasis n 0 m c p))))=0
  rw [occupationTripleCoefficients_basis,hL,map_zero,map_zero]

theorem physicalTripleLeftRadialTotal_zero_middle (q : ℝ) (n l c : ℕ) :
    physicalTripleLeftRadialTotal q n l 0 c=0 := by
  apply (occupationTripleBasis n l 0 c).ext
  intro p
  have hL : tripleLeftAnnihilation q n (Finsupp.single (occupationTripleEmbedding n l 0 c p) 1)=0 := by
    simp only [tripleLeftAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hz:=occupationWeight_zero_coordinate n p.2.1 i
    simp only [tripleLeftAnnihilationCoefficient,mixedAnnihilationCoefficient,occupationTripleEmbedding] at *
    rw [hz,qInteger_zero]
    simp only [mul_zero,zero_mul,Finsupp.single_zero]
  change occupationTripleSynthesis n l 0 c
    (tripleLeftCreation q n (tripleLeftAnnihilation q n
      (occupationTripleCoefficients n l 0 c (occupationTripleBasis n l 0 c p))))=0
  rw [occupationTripleCoefficients_basis,hL,map_zero,map_zero]

theorem physicalTripleRightRadialTotal_zero_middle (q : ℝ) (n l c : ℕ) :
    physicalTripleRightRadialTotal q n l 0 c=0 := by
  apply (occupationTripleBasis n l 0 c).ext
  intro p
  have hL : tripleRightAnnihilation q n (Finsupp.single (occupationTripleEmbedding n l 0 c p) 1)=0 := by
    simp only [tripleRightAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hz:=occupationWeight_zero_coordinate n p.2.1 i
    simp only [tripleRightAnnihilationCoefficient,mixedAnnihilationCoefficient,occupationTripleEmbedding,occupationLatticeReflect,Fin.rev_rev] at *
    rw [hz,qInteger_zero]
    simp only [mul_zero,zero_mul,Finsupp.single_zero]
  change occupationTripleSynthesis n l 0 c
    (tripleRightCreation q n (tripleRightAnnihilation q n
      (occupationTripleCoefficients n l 0 c (occupationTripleBasis n l 0 c p))))=0
  rw [occupationTripleCoefficients_basis,hL,map_zero,map_zero]

theorem physicalTripleRightRadialTotal_zero_third (q : ℝ) (n l m : ℕ) :
    physicalTripleRightRadialTotal q n l m 0=0 := by
  apply (occupationTripleBasis n l m 0).ext
  intro p
  have hL : tripleRightAnnihilation q n (Finsupp.single (occupationTripleEmbedding n l m 0 p) 1)=0 := by
    simp only [tripleRightAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hz:=occupationWeight_zero_coordinate n p.2.2 i
    simp only [tripleRightAnnihilationCoefficient,mixedAnnihilationCoefficient,occupationTripleEmbedding,occupationLatticeReflect,Fin.rev_rev] at *
    rw [hz,qInteger_zero]
    simp only [mul_zero,zero_mul,Finsupp.single_zero]
  change occupationTripleSynthesis n l m 0
    (tripleRightCreation q n (tripleRightAnnihilation q n
      (occupationTripleCoefficients n l m 0 (occupationTripleBasis n l m 0 p))))=0
  rw [occupationTripleCoefficients_basis,hL,map_zero,map_zero]

end AMSPhysical
#print axioms AMSPhysical.physicalTripleLeftRadialTotal_zero_first
#print axioms AMSPhysical.physicalTripleRightRadialTotal_zero_third

