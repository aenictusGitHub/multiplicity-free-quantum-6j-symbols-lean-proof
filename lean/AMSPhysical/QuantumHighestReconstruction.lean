import QuantumRacahOrthogonality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

theorem orthonormal_basis_reconstruct (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Basis ι ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) (p : V) :
    (∑ i,B p (b i) • b i)=p := by
  simp only [orthonormal_basis_coord_left B b hb]
  exact b.sum_repr p

/-- Actual highest-weight recoupling identity; no closed formula for its entries is assumed. -/
theorem quantumHighest_recoupling_identity (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    (∑ a : RightHighestPath l m n,quantumRacahMatrix q hq hq1 l m n p a •
      quantumRightTreeHighest q hq hq1 l m n a.1 a.2)=quantumLeftTreeHighest q hq hq1 l m n p.1 p.2 := by
  have hb (i j : RightFusionIndex l m n) : quantumTripleBilin q l m n
      (quantumRightFusionBasis q hq hq1 l m n i) (quantumRightFusionBasis q hq hq1 l m n j)=if i=j then 1 else 0 := by
    rw [quantumRightFusionBasis_apply,quantumRightFusionBasis_apply]
    exact rightFusionVector_pair q hq hq1 l m n i j
  have hf : (∑ k : RightFusionIndex l m n,
      fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) k •
        rightFusionVector q hq hq1 l m n k)=quantumLeftTreeHighest q hq hq1 l m n p.1 p.2 := by
    have he := orthonormal_basis_reconstruct (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
      (quantumRightFusionBasis q hq hq1 l m n) hb (leftFusionVector q hq hq1 l m n (leftHighestEmbedding l m n p))
    simpa only [quantumRightFusionBasis_apply,fullQuantumRecouplingMatrix,leftFusionHighest_eq] using he
  have hs : (∑ k : RightFusionIndex l m n,
      fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) k •
        rightFusionVector q hq hq1 l m n k)=
      ∑ a : RightHighestPath l m n,quantumRacahMatrix q hq hq1 l m n p a •
        quantumRightTreeHighest q hq hq1 l m n a.1 a.2 := by
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [Fin.sum_univ_succ]
    have hz : (∑ k : Fin (coupledLabel l (coupledLabel m n u) v),
        fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) ⟨u,⟨v,k.succ⟩⟩ •
          rightFusionVector q hq hq1 l m n ⟨u,⟨v,k.succ⟩⟩)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [fullRecoupling_highest_rightLower_zero q hq hq1 l m n p ⟨u,v⟩ k,zero_smul]
    rw [hz,add_zero]
    change fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p)
      (rightHighestEmbedding l m n ⟨u,v⟩) • rightFusionVector q hq hq1 l m n (rightHighestEmbedding l m n ⟨u,v⟩)=_
    rw [fullRecoupling_highest_eq,rightFusionHighest_eq]
  rw [hs] at hf
  exact hf

end AMSPhysical

#print axioms AMSPhysical.quantumHighest_recoupling_identity
