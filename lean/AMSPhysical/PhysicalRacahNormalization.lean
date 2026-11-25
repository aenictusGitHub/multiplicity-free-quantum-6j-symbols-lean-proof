import RacahBoundaryPhysical
import PhysicalAMSLabels

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The physical factorial prefactor has precisely the conventional quantum
dimension and four triangle factors, with its positive sign proved. -/
theorem physicalRacahClosedPrefactor_standard (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n H : ℕ) (first : FixedLeftHighest l m n H)
    (hb : first.val.1.val=0 ∨ first.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H)
    (p : FixedLeftHighest l m n H) :
    physicalRacahClosedPrefactor q l m n H first p a=standardRacahPrefactor q l m n p.val a := by
  have hF := quantumRacahMatrix_closed_factorial_sum q hq hq1 l m n H first hb a hH first
  have hS : spinRacahFactorialSum q l m n (leftHighestDefect l m n H) a.1.val first.val.1.val first.val.2.val≠0 := by
    intro hz
    rw [hz,mul_zero] at hF
    exact (ne_of_gt (quantumRacah_boundary_pos q hq hq1 l m n H first hb a hH)) hF
  have hB := physical_boundary_triangle_square q hq l m n H first hb a hH
  rw [← quantumRacah_boundary_factorial q hq hq1 l m n H first hb a hH,hF,mul_pow] at hB
  have hfirst : (physicalRacahClosedPrefactor q l m n H first first a)^2=
      leftRacahTriangleWeight q l m n first.val*rightRacahTriangleWeight q l m n a :=
    mul_right_cancel₀ (pow_ne_zero 2 hS) hB
  have hr := physicalRacahPrefactor_square_ratio q hq l m n H first p a
  rw [hfirst] at hr
  have hpsq : (physicalRacahClosedPrefactor q l m n H first p a)^2=
      leftRacahTriangleWeight q l m n p.val*rightRacahTriangleWeight q l m n a := by
    apply mul_right_cancel₀ (ne_of_gt (leftRacahTriangleWeight_pos q hq l m n first.val))
    linear_combination hr
  unfold standardRacahPrefactor
  rw [← hpsq,Real.sqrt_sq_eq_abs,abs_of_pos (physicalRacahClosedPrefactor_pos q hq l m n H first p a)]

/-- The conventional signed, dimension-normalized physical Racah coefficient
has the exact AMS rank-two factorial kernel. -/
theorem physical_rank_two_AMS_standard (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    quantumRacahMatrix q hq hq1 l m n p.val a=
      (-1:ℝ)^(l+m+n-leftHighestDefect l m n H)*standardRacahPrefactor q l m n p.val a*
        AMSGeneral.kernel (quantumFactorialInt q) 0 false (l:ℤ) m n H
          (coupledLabel l m p.val.1) (coupledLabel m n a.1) := by
  obtain ⟨first,hb⟩ := fixedLeftHighest_first_exists l m n H p
  rw [physical_rank_two_AMS_kernel q hq hq1 l m n H first hb a hH p,
    physicalRacahClosedPrefactor_standard q hq hq1 l m n H first hb a hH p]

end AMSPhysical

#print axioms AMSPhysical.physical_rank_two_AMS_standard
