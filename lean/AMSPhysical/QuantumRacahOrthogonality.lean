import QuantumFusionHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module

theorem quantumRacah_rows (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p v : LeftHighestPath l m n) :
    (∑ a,quantumRacahMatrix q hq hq1 l m n p a*quantumRacahMatrix q hq hq1 l m n v a)=
      if p=v then 1 else 0 := by
  have he := fullQuantumRecoupling_rows q hq hq1 l m n (leftHighestEmbedding l m n p) (leftHighestEmbedding l m n v)
  have hs : (∑ k : RightFusionIndex l m n,
      fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) k*
      fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n v) k)=
      ∑ a : RightHighestPath l m n,quantumRacahMatrix q hq hq1 l m n p a*quantumRacahMatrix q hq hq1 l m n v a := by
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro a ha
    rw [Fin.sum_univ_succ]
    have hz : (∑ k : Fin (coupledLabel l (coupledLabel m n u) a),
        fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) ⟨u,⟨a,k.succ⟩⟩*
        fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n v) ⟨u,⟨a,k.succ⟩⟩)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [fullRecoupling_highest_rightLower_zero q hq hq1 l m n p ⟨u,a⟩ k,zero_mul]
    rw [hz,add_zero]
    exact congrArg₂ (·*·) (fullRecoupling_highest_eq q hq hq1 l m n p ⟨u,a⟩)
      (fullRecoupling_highest_eq q hq hq1 l m n v ⟨u,a⟩)
  rw [hs] at he
  simpa only [(leftHighestEmbedding_injective l m n).eq_iff] using he

theorem quantumRacah_cols (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p v : RightHighestPath l m n) :
    (∑ a,quantumRacahMatrix q hq hq1 l m n a p*quantumRacahMatrix q hq hq1 l m n a v)=
      if p=v then 1 else 0 := by
  have he := fullQuantumRecoupling_cols q hq hq1 l m n (rightHighestEmbedding l m n p) (rightHighestEmbedding l m n v)
  have hs : (∑ k : LeftFusionIndex l m n,
      fullQuantumRecouplingMatrix q hq hq1 l m n k (rightHighestEmbedding l m n p)*
      fullQuantumRecouplingMatrix q hq hq1 l m n k (rightHighestEmbedding l m n v))=
      ∑ a : LeftHighestPath l m n,quantumRacahMatrix q hq hq1 l m n a p*quantumRacahMatrix q hq hq1 l m n a v := by
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro a ha
    rw [Fin.sum_univ_succ]
    have hz : (∑ k : Fin (coupledLabel (coupledLabel l m r) n a),
        fullQuantumRecouplingMatrix q hq hq1 l m n ⟨r,⟨a,k.succ⟩⟩ (rightHighestEmbedding l m n p)*
        fullQuantumRecouplingMatrix q hq hq1 l m n ⟨r,⟨a,k.succ⟩⟩ (rightHighestEmbedding l m n v))=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [fullRecoupling_leftLower_highest_zero q hq hq1 l m n p ⟨r,a⟩ k,zero_mul]
    rw [hz,add_zero]
    exact congrArg₂ (·*·) (fullRecoupling_highest_eq q hq hq1 l m n ⟨r,a⟩ p)
      (fullRecoupling_highest_eq q hq hq1 l m n ⟨r,a⟩ v)
  rw [hs] at he
  simpa only [(rightHighestEmbedding_injective l m n).eq_iff] using he

theorem quantumRacah_mul_transpose (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    quantumRacahMatrix q hq hq1 l m n*(quantumRacahMatrix q hq hq1 l m n).transpose=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
  exact quantumRacah_rows q hq hq1 l m n i j

theorem quantumRacah_transpose_mul (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    (quantumRacahMatrix q hq hq1 l m n).transpose*quantumRacahMatrix q hq hq1 l m n=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
  exact quantumRacah_cols q hq hq1 l m n i j

/-- Total highest weight is preserved by the actual recoupling matrix. -/
theorem quantumRacah_total_selection (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (v : RightHighestPath l m n)
    (h : coupledLabel (coupledLabel l m p.1) n p.2≠coupledLabel l (coupledLabel m n v.1) v.2) :
    quantumRacahMatrix q hq hq1 l m n p v=0 := by
  apply pairAdjoint_eigen_orthogonal (V:=RealQuantumTripleSpace l m n)
    (finiteTripleRepresentation_compact q hq hq1 l m n).adjK
    (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2) (quantumRightTreeHighest q hq hq1 l m n v.1 v.2)
    (q^(coupledLabel (coupledLabel l m p.1) n p.2:ℤ)) (q^(coupledLabel l (coupledLabel m n v.1) v.2:ℤ))
    (quantumLeftTreeHighest_K q hq hq1 l m n p) (quantumRightTreeHighest_K q hq hq1 l m n v)
  intro he
  exact h (Int.ofNat_inj.mp (zpow_right_injective₀ hq hq1 he))

end AMSPhysical

#print axioms AMSPhysical.quantumRacah_mul_transpose
#print axioms AMSPhysical.quantumRacah_transpose_mul
#print axioms AMSPhysical.quantumRacah_total_selection
