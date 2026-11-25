import QuantumMixedFusionWeight
import QuantumMixedHighestExpansion
import KroneckerEigenExpansion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedBoundaryFunctional (n l m : ℕ) (r : MixedFusionIndex l m) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ] ℝ :=
  (Finsupp.lapply ((highestOccupation n l).val,(mixedBoundaryAt n l m r).val)).comp
    (occupationTensorCoefficients n l m)

theorem mixedBoundaryFunctional_highest (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r s : MixedFusionIndex l m) :
    mixedBoundaryFunctional n l m r (mixedFusionHighestAt q n l m s)=(if s=r then 1 else 0) := by
  change occupationTensorCoefficients n l m (mixedFusionHighestAt q n l m s)
    ((highestOccupation n l).val,(mixedBoundaryAt n l m r).val)=_
  rw [mixedFusionHighestAt_boundary q hq n hn]
  simp only [(mixedBoundaryAt_injective n l m hn).eq_iff]

theorem mixedFusionHighestAt_linearIndependent (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    LinearIndependent ℝ (mixedFusionHighestAt q n l m) :=
  linearIndependent_of_kronecker_functionals (mixedFusionHighestAt q n l m)
    (mixedBoundaryFunctional n l m) (mixedBoundaryFunctional_highest q hq n hn l m)

theorem mixedFusionHighestAt_full_weight_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (hK : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 2) v=q^(mixedHighestDynkin n (l-r.val) (m-r.val) i) • v) :
    v=mixedBoundaryFunctional n l m r v • mixedFusionHighestAt q n l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let i : Fin n := ⟨0,hn⟩
  let lam := fun s : MixedFusionIndex l m =>q^(mixedHighestDynkin n (l-s.val) (m-s.val) i)
  have hLam : Function.Injective lam := by
    intro s t he
    apply mixedFusionHighest_first_weight_injective n hn l m
    exact zpow_right_injective₀ hq hq1 he
  apply eigenvector_of_distinct_expansion (V:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 2))
    (mixedFusionHighestAt q n l m) lam (mixedFusionHighestAt_linearIndependent q hq n hn l m) hLam
    (fun s => mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m s i)
    v (fun s => mixedBoundaryFunctional n l m s v) r
  · exact mixedHighest_complete_expansion q hq hq1 n hn l m v hE
  · exact hK i

end AMSPhysical
