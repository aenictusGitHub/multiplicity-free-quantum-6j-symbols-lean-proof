import QuantumTripleCreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLeftCreation_power_first_boundary (q : ℝ) (hq : q≠0) (n : ℕ) (l : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f)
    (y z : Fin (n+1) → ℤ) (t : ℕ) :
    ((tripleLeftCreation q n)^t) f (Pi.single 0 (l+(t:ℤ)),y+Pi.single 0 (t:ℤ),z)=
      q^(-(l+y 0)*(t:ℤ)-(t:ℤ)^2+(t:ℤ))*f (Pi.single 0 l,y,z) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hP : ((tripleLeftCreation q n)^(t+1)) f=
        tripleLeftCreation q n (((tripleLeftCreation q n)^t) f) :=
      DFunLike.congr_fun (pow_succ' (tripleLeftCreation q n) t) f
    have hpoint : ((Pi.single 0 (l+((t+1:ℕ):ℤ)),y+Pi.single 0 ((t+1:ℕ):ℤ),z) : OccupationTripleLattice n)=
        (Pi.single 0 ((l+(t:ℤ))+1),(y+Pi.single 0 (t:ℤ))+Pi.single 0 1,z) := by
      ext i <;> simp [Pi.single_apply] <;> split_ifs <;> push_cast <;> ring
    rw [hP,hpoint,tripleLeftCreation_first_boundary q n (l+(t:ℤ)) _
      (coefficientSupported_pow (tripleOccupationNonnegative n) (tripleLeftCreation q n)
        (tripleLeftCreation_nonnegative_support q n) f hf t),ih]
    simp only [Pi.add_apply,Pi.single_eq_same]
    rw [← mul_assoc,← zpow_add₀ hq]
    congr 1
    congr 1
    push_cast
    ring

theorem tripleRightCreation_power_middle_boundary (q : ℝ) (hq : q≠0) (n : ℕ) (h : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f)
    (x z : Fin (n+1) → ℤ) (t : ℕ) :
    ((tripleRightCreation q n)^t) f (x,Pi.single (Fin.last n) (h+(t:ℤ)),z+Pi.single (Fin.last n) (t:ℤ))=
      q^(-(h+z (Fin.last n))*(t:ℤ)-(t:ℤ)^2+(t:ℤ))*f (x,Pi.single (Fin.last n) h,z) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hP : ((tripleRightCreation q n)^(t+1)) f=
        tripleRightCreation q n (((tripleRightCreation q n)^t) f) :=
      DFunLike.congr_fun (pow_succ' (tripleRightCreation q n) t) f
    have hpoint : ((x,Pi.single (Fin.last n) (h+((t+1:ℕ):ℤ)),z+Pi.single (Fin.last n) ((t+1:ℕ):ℤ)) : OccupationTripleLattice n)=
        (x,Pi.single (Fin.last n) ((h+(t:ℤ))+1),(z+Pi.single (Fin.last n) (t:ℤ))+Pi.single (Fin.last n) 1) := by
      ext i <;> simp [Pi.single_apply] <;> split_ifs <;> push_cast <;> ring
    rw [hP,hpoint,tripleRightCreation_middle_boundary q n (h+(t:ℤ)) _
      (coefficientSupported_pow (tripleOccupationNonnegative n) (tripleRightCreation q n)
        (tripleRightCreation_nonnegative_support q n) f hf t),ih]
    simp only [Pi.add_apply,Pi.single_eq_same]
    rw [← mul_assoc,← zpow_add₀ hq]
    congr 1
    congr 1
    push_cast
    ring

end AMSPhysical
