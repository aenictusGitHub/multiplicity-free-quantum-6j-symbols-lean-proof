import BilinearCyclicIrreducible
import QuantumMixedCompact
import QuantumMixedWeightSpace
import QuantumMixedHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedChannelSubmodule (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :=
  algebraCyclicSpan (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) (typeAMixedTensor q hq hD n (r+a) (r+b)) (mixedHighestVector q n r a b)

theorem mixedChannelSubmodule_invariant (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    algebraInvariant (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) (typeAMixedTensor q hq hD n (r+a) (r+b)) (mixedChannelSubmodule q hq hD n r a b) :=
  algebraCyclicSpan_invariant _ _

theorem mixedChannelSubmodule_ne_bot (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    mixedChannelSubmodule q (ne_of_gt hq) hD n r a b≠⊥ := by
  intro hz
  have hm := algebraCyclicSpan_self (typeAMixedTensor q (ne_of_gt hq) hD n (r+a) (r+b))
    (mixedHighestVector q n r a b)
  change mixedHighestVector q n r a b∈mixedChannelSubmodule q (ne_of_gt hq) hD n r a b at hm
  rw [hz,Submodule.mem_bot] at hm
  exact mixedHighestVector_ne_zero q hq n r a b hm

/-- Genuine irreducibility of every constructed mixed channel, proved from
the actual full tensor action, positive compact form and full highest-line
uniqueness. No simple-module decomposition is assumed. -/
theorem mixedChannelSubmodule_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ) (hn : 0<n)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) (r+b)))
    (hSC : S≤mixedChannelSubmodule q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b)
    (hS : algebraInvariant (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b)) S) :
    S=⊥ ∨ S=mixedChannelSubmodule q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b := by
  exact cyclic_highest_irreducible (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b))
    (mixedTensorBilin q n (r+a) (r+b)) (mixedTensorBilin_symm q n (r+a) (r+b))
    (mixedTensorBilin_definite q hq n (r+a) (r+b))
    (typeAMixedTensor_compact q hq hq1 n (r+a) (r+b)).adjoint_exists
    (fun i : Fin n => typeAAlgebraGenerator q n i 0) (fun i : Fin n => typeAAlgebraGenerator q n i 2)
    (fun i : Fin n => q^(mixedHighestDynkin n a b i)) (mixedHighestVector q n r a b)
    (mixedHighestVector_E_zero q hq hq1 n r a b)
    (mixedHighestVector_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b)
    (fun w hE hK => mixedHighest_full_weight_unique q hq hq1 n r a b hn w hK hE) S hSC hS

end AMSPhysical
#print axioms AMSPhysical.mixedChannelSubmodule_irreducible
