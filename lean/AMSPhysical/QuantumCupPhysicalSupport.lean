import QuantumTripleCoordinateDegrees
import QuantumCupIndependent

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupMonomial_coordinate_homogeneous (q : ℝ) (n : ℕ) (l h c : ℤ) (t k : ℕ) (j : Fin 3) :
    CoefficientHomogeneous (tripleCoordinateDegree n j) (![l,h+(t:ℤ)+(k:ℤ),c] j)
      (quantumCupMonomial q n l h c t k) := by
  let a := tripleCoordinateDegree n j (Pi.single 0 (l-(t:ℤ)),Pi.single (Fin.last n) h,Pi.single 0 (c-(k:ℤ)))
  have h0:=coefficientHomogeneous_single (tripleCoordinateDegree n j)
    (Pi.single 0 (l-(t:ℤ)),Pi.single (Fin.last n) h,Pi.single 0 (c-(k:ℤ))) 1
  have hR:=gradedCreation_pow (tripleCoordinateDegree n j) (tripleRightCreation q n) (![0,1,1] j)
    (tripleRightCreation_coordinate_homogeneous q n j) a _ h0 k
  have hL:=gradedCreation_pow (tripleCoordinateDegree n j) (tripleLeftCreation q n) (![1,1,0] j)
    (tripleLeftCreation_coordinate_homogeneous q n j) (a+![0,1,1] j*(k:ℤ)) _ hR t
  have he : (a+![0,1,1] j*(k:ℤ))+![1,1,0] j*(t:ℤ)=![l,h+(t:ℤ)+(k:ℤ),c] j := by
    dsimp only [a]
    rw [tripleCoordinateDegree_cupBase]
    fin_cases j <;> simp <;> ring
  rw [he] at hL
  exact hL

theorem quantumCupMonomialAt_nonnegative_support (q : ℝ) (n l m h c : ℕ) (r : QuantumCupIndex l m c) :
    CoefficientSupported (tripleOccupationNonnegative n) (quantumCupMonomialAt q n l m h c r) := by
  apply coefficientSupported_pow _ _ (tripleLeftCreation_nonnegative_support q n)
  apply coefficientSupported_pow _ _ (tripleRightCreation_nonnegative_support q n)
  apply tripleCupBase_nonnegative_support
  · have hl:=r.property.1;omega
  · omega
  · have hc:=r.property.2;omega

/-- Every cup monomial has literal nonnegative occupations of the physical
external degrees (l,m+h,c); this is proved rather than imposed by truncation. -/
theorem quantumCupMonomialAt_physical_support (q : ℝ) (n l m h c : ℕ) (r : QuantumCupIndex l m c)
    (p : OccupationTripleLattice n) (hp : quantumCupMonomialAt q n l m h c r p≠0) :
    p.1∈occupationWeights (Fin (n+1)) l ∧ p.2.1∈occupationWeights (Fin (n+1)) (m+h) ∧
      p.2.2∈occupationWeights (Fin (n+1)) c := by
  have hpos:=quantumCupMonomialAt_nonnegative_support q n l m h c r p hp
  have hdeg:=fun j : Fin 3 =>quantumCupMonomial_coordinate_homogeneous q n (l:ℤ) (h:ℤ) (c:ℤ)
    r.val.val (m-r.val.val) j p hp
  have h0:=hdeg 0
  have h1:=hdeg 1
  have h2:=hdeg 2
  simp only [tripleCoordinateDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at h0 h1 h2
  constructor
  · exact ⟨hpos.1,h0⟩
  · constructor
    · refine ⟨hpos.2.1,?_⟩
      have ht:=r.val.isLt
      omega
    · exact ⟨hpos.2.2,h2⟩

end AMSPhysical
