import QuantumHighestSpan
import QuantumProjectedTriangular

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module

abbrev FixedLeftHighest (l m n H : ℕ) := {p : LeftHighestPath l m n // leftTotalLabel l m n p=H}

def leftHighestDefect (l m n H : ℕ) : ℕ := (l+m+n-H)/2

theorem leftTotalLabel_defect (l m n : ℕ) (p : LeftHighestPath l m n) :
    l+m+n=leftTotalLabel l m n p+2*(p.1.val+p.2.val) := by
  have hl := channel_left_bound l m p.1
  have hm := channel_right_bound l m p.1
  have hi := channel_left_bound (coupledLabel l m p.1) n p.2
  have hn := channel_right_bound (coupledLabel l m p.1) n p.2
  unfold leftTotalLabel coupledLabel at *
  omega

theorem fixedLeftHighest_defect (l m n H : ℕ) (p : FixedLeftHighest l m n H) :
    p.val.1.val+p.val.2.val=leftHighestDefect l m n H := by
  have hh := leftTotalLabel_defect l m n p.val
  rw [p.property] at hh
  unfold leftHighestDefect
  omega

theorem fixedLeftHighest_index_injective (l m n H : ℕ) :
    Function.Injective (fun p : FixedLeftHighest l m n H => p.val.1.val) := by
  intro p v he
  apply Subtype.ext
  have hfirst : p.val.1=v.val.1 := Fin.ext he
  rcases p with ⟨⟨r,s⟩,hp⟩
  rcases v with ⟨⟨r',s'⟩,hv⟩
  dsimp only at hfirst
  subst r'
  have hs : s=s' := by
    apply Fin.ext
    have h₁ := leftTotalLabel_defect l m n ⟨r,s⟩
    have h₂ := leftTotalLabel_defect l m n ⟨r,s'⟩
    change leftTotalLabel l m n ⟨r,s⟩=H at hp
    change leftTotalLabel l m n ⟨r,s'⟩=H at hv
    rw [hp] at h₁
    rw [hv] at h₂
    change l+m+n=H+2*(r.val+s.val) at h₁
    change l+m+n=H+2*(r.val+s'.val) at h₂
    omega
  subst s'
  rfl

/-- Restrict the proved highest expansion to the specified total irrep. -/
theorem quantumHighest_fixed_left_expansion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (v : RealQuantumTripleSpace l m n)
    (hE : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 0) v=0)
    (hK : finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 2) v=q^(H:ℤ) • v) :
    (∑ p : FixedLeftHighest l m n H,quantumTripleBilin q l m n v
      (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2) •
        quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2)=v := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun p : LeftHighestPath l m n => leftTotalLabel l m n p=H)
    (fun p : LeftHighestPath l m n => quantumTripleBilin q l m n v
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2) • quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)
  have hz : (∑ p : {p : LeftHighestPath l m n // ¬leftTotalLabel l m n p=H},
      quantumTripleBilin q l m n v (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2) •
        quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2)=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [quantumHighest_left_total_selection q hq hq1 l m n H v hK p.val
      (Ne.symm p.property),zero_smul]
  rw [hz,add_zero,quantumHighest_left_expansion q hq hq1 l m n H v hE hK] at he
  exact he

/-- Coordinate functionals at fixed total defect, used to derive the actual Jacobi matrix. -/
def fixedHighestCoordinate (l m n H y : ℕ) : RealQuantumTripleSpace l m n →ₗ[ℝ] ℝ :=
  (finiteTensorCoefficient m n (y:ℤ) ((leftHighestDefect l m n H:ℤ)-(y:ℤ))).comp
    (firstTripleProjection l m n)

theorem fixedHighestCoordinate_triangular (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (y : ℕ) (hy : y<p.val.1.val) :
    fixedHighestCoordinate l m n H y (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2)=0 := by
  exact quantumLeftTreeHighest_projected_below q hq hq1 l m n p.val y _ (by omega)

theorem fixedHighestCoordinate_diagonal_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) :
    0<fixedHighestCoordinate l m n H p.val.1.val
      (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2) := by
  unfold fixedHighestCoordinate
  rw [LinearMap.comp_apply]
  have hi : (leftHighestDefect l m n H:ℤ)-(p.val.1.val:ℤ)=(p.val.2.val:ℤ) := by
    have h := fixedLeftHighest_defect l m n H p
    omega
  rw [hi]
  exact quantumLeftTreeHighest_projected_leading_pos q hq hq1 l m n p.val

end AMSPhysical

#print axioms AMSPhysical.quantumHighest_fixed_left_expansion
#print axioms AMSPhysical.fixedHighestCoordinate_diagonal_pos
