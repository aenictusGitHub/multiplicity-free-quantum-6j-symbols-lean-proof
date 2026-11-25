import TwoRowHighestWeight
import QuantumSymmetricHighestExpansion
import KroneckerEigenExpansion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoRowBoundaryFunctional (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ] ℝ :=
  (Finsupp.lapply ((highestOccupation n l).val,(twoRowBoundaryAt n hn l m r).val)).comp
    (occupationTensorCoefficients n l m)

theorem twoRowBoundaryFunctional_highest (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r s : TwoRowFusionIndex l m) :
    twoRowBoundaryFunctional n hn l m r (twoRowHighestAt q n hn l m s)=(if s=r then 1 else 0) := by
  change occupationTensorCoefficients n l m (twoRowHighestAt q n hn l m s)
    ((highestOccupation n l).val,(twoRowBoundaryAt n hn l m r).val)=_
  rw [twoRowHighestAt_boundary]
  simp only [(twoRowBoundaryAt_injective n hn l m).eq_iff]

theorem twoRowHighestAt_linearIndependent (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    LinearIndependent ℝ (twoRowHighestAt q n hn l m) :=
  linearIndependent_of_kronecker_functionals (twoRowHighestAt q n hn l m)
    (twoRowBoundaryFunctional n hn l m) (twoRowBoundaryFunctional_highest q n hn l m)

/-- Full highest-line uniqueness for each physical two-row label, in the
entire tensor product and with no assumed support or fusion rule. -/
theorem twoRowHighestAt_full_weight_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (hK : ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 2) v=q^(twoRowHighestWeight n hn l m r.val i) • v) :
    ∃ a : ℝ,v=a • twoRowHighestAt q n hn l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let i : Fin n := ⟨0,hn⟩
  let lam := fun s : TwoRowFusionIndex l m =>q^(twoRowHighestWeight n hn l m s.val i)
  have hLam : Function.Injective lam := by
    intro s t he
    apply twoRowHighest_first_weight_injective n hn l m
    exact zpow_right_injective₀ hq hq1 he
  refine ⟨twoRowBoundaryFunctional n hn l m r v,?_⟩
  apply eigenvector_of_distinct_expansion (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 2))
    (twoRowHighestAt q n hn l m) lam (twoRowHighestAt_linearIndependent q n hn l m) hLam
    (fun s => twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m s i)
    v (fun s => twoRowBoundaryFunctional n hn l m s v) r
  · exact symmetricHighest_complete_expansion q hq hq1 n hn l m v hE
  · exact hK i

end AMSPhysical
#print axioms AMSPhysical.twoRowHighestAt_full_weight_unique
