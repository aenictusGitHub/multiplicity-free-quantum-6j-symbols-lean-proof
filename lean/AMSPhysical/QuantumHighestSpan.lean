import QuantumHighestReconstruction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module

def leftTotalLabel (l m n : ℕ) (p : LeftHighestPath l m n) : ℕ :=
  coupledLabel (coupledLabel l m p.1) n p.2

theorem quantumHighest_left_lower_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (v : RealQuantumTripleSpace l m n)
    (hE : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 0) v=0)
    (hK : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 2) v=q^(H:ℤ) • v)
    (p : LeftHighestPath l m n) (k : Fin (leftTotalLabel l m n p)) :
    quantumTripleBilin q l m n v (leftFusionVector q hq hq1 l m n ⟨p.1,⟨p.2,k.succ⟩⟩)=0 := by
  exact quantumHighest_orthogonal_orthonormalLower (W:=RealQuantumTripleSpace l m n) q hq hq1 H
    (leftTotalLabel l m n p) (quantumTripleBilin q l m n) (quantumTripleBilin_symm q hq hq1 l m n)
    (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
    (finiteTripleRepresentation_compact q hq hq1 l m n) v hE hK
    (quantumLeftTreeMap q hq hq1 l m n p.1 p.2) (quantumLeftTreeMap_intertwines q hq hq1 l m n p.1 p.2) k

/-- The actual left coupling highest vectors span every highest-weight vector. -/
theorem quantumHighest_left_expansion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (v : RealQuantumTripleSpace l m n)
    (hE : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 0) v=0)
    (hK : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 2) v=q^(H:ℤ) • v) :
    (∑ p : LeftHighestPath l m n,quantumTripleBilin q l m n v (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2) •
      quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)=v := by
  have hb (i j : LeftFusionIndex l m n) : quantumTripleBilin q l m n
      (quantumLeftFusionBasis q hq hq1 l m n i) (quantumLeftFusionBasis q hq hq1 l m n j)=if i=j then 1 else 0 := by
    rw [quantumLeftFusionBasis_apply,quantumLeftFusionBasis_apply]
    exact leftFusionVector_pair q hq hq1 l m n i j
  have hf := orthonormal_basis_reconstruct (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
    (quantumLeftFusionBasis q hq hq1 l m n) hb v
  simp only [quantumLeftFusionBasis_apply] at hf
  have hs : (∑ k : LeftFusionIndex l m n,quantumTripleBilin q l m n v (leftFusionVector q hq hq1 l m n k) •
      leftFusionVector q hq hq1 l m n k)=
      ∑ p : LeftHighestPath l m n,quantumTripleBilin q l m n v (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2) •
        quantumLeftTreeHighest q hq hq1 l m n p.1 p.2 := by
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    rw [Fin.sum_univ_succ]
    have hz : (∑ k : Fin (coupledLabel (coupledLabel l m r) n s),
        quantumTripleBilin q l m n v (leftFusionVector q hq hq1 l m n ⟨r,⟨s,k.succ⟩⟩) •
          leftFusionVector q hq hq1 l m n ⟨r,⟨s,k.succ⟩⟩)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [quantumHighest_left_lower_zero q hq hq1 l m n H v hE hK ⟨r,s⟩ k,zero_smul]
    rw [hz,add_zero]
    change quantumTripleBilin q l m n v (leftFusionVector q hq hq1 l m n (leftHighestEmbedding l m n ⟨r,s⟩)) •
      leftFusionVector q hq hq1 l m n (leftHighestEmbedding l m n ⟨r,s⟩)=_
    rw [leftFusionHighest_eq]
  rw [hs] at hf
  exact hf

theorem quantumHighest_left_total_selection (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (v : RealQuantumTripleSpace l m n)
    (hK : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 2) v=q^(H:ℤ) • v)
    (p : LeftHighestPath l m n) (hne : H≠leftTotalLabel l m n p) :
    quantumTripleBilin q l m n v (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)=0 := by
  apply pairAdjoint_eigen_orthogonal (V:=RealQuantumTripleSpace l m n)
    (finiteTripleRepresentation_compact q hq hq1 l m n).adjK v _
    (q^(H:ℤ)) (q^(leftTotalLabel l m n p:ℤ)) hK (quantumLeftTreeHighest_K q hq hq1 l m n p)
  intro he
  exact hne (Int.ofNat_inj.mp (zpow_right_injective₀ hq hq1 he))

end AMSPhysical

#print axioms AMSPhysical.quantumHighest_left_expansion
