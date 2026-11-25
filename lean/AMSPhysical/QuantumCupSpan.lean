import QuantumCupIndependent
import QuantumCupRankShiftCoefficients
import IndependentSpanTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupSpan (q : ℝ) (n l m h c : ℕ) : Submodule ℝ (OccupationTripleLattice n →₀ ℝ) :=
  Submodule.span ℝ (Set.range (quantumCupMonomialAt q n l m h c))

def quantumCupVector (q : ℝ) (n l m h c : ℕ) (r : QuantumCupIndex l m c) : quantumCupSpan q n l m h c :=
  ⟨quantumCupMonomialAt q n l m h c r,Submodule.subset_span (Set.mem_range_self r)⟩

def quantumCupBasis (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Module.Basis (QuantumCupIndex l m c) ℝ (quantumCupSpan q n l m h c) :=
  Module.Basis.span (quantumCupMonomialAt_linearIndependent q hq n hn l m h c)

theorem quantumCupBasis_apply (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    quantumCupBasis q hq n hn l m h c r=quantumCupVector q n l m h c r :=
  Subtype.ext (Module.Basis.span_apply _ r)

/-- An actual bijection between independently proved occupation cup spans.
The physical metric and full highest-space completeness remain separate obligations. -/
def quantumCupRankReduction (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    quantumCupSpan q n l m h c ≃ₗ[ℝ] quantumCupSpan q 1 l m (h+n-1) c :=
  independentSpanTransport (quantumCupMonomialAt q n l m h c)
    (quantumCupMonomialAt q 1 l m (h+n-1) c)
    (quantumCupMonomialAt_linearIndependent q hq n hn l m h c)
    (quantumCupMonomialAt_linearIndependent q hq 1 (by omega) l m (h+n-1) c)
    (fun r =>quantumCupRankGauge n r.val.val) (fun r =>quantumCupRankGauge_ne_zero n r.val.val)

theorem quantumCupRankReduction_vector (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    quantumCupRankReduction q hq n hn l m h c (quantumCupVector q n l m h c r)=
      quantumCupRankGauge n r.val.val • quantumCupVector q 1 l m (h+n-1) c r := by
  apply Subtype.ext
  exact independentSpanTransport_basis _ _ _ _ _ _ r

end AMSPhysical
