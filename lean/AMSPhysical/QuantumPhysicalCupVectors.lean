import QuantumCupPhysicalSupport
import OccupationTripleCoefficients
import IndependentSpanTransport
import QuantumCupSpan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

/-- A literal vector in Sym_l tensor Opp_(m+h) tensor Sym_c, specified by
the proved physical occupation support of the independently constructed cups. -/
def physicalQuantumCupVector (q : ℝ) (n l m h c : ℕ) (r : QuantumCupIndex l m c) :
    quantumOccupationTripleSpace n l (m+h) c :=
  occupationTripleSynthesis n l (m+h) c (quantumCupMonomialAt q n l m h c r)

theorem occupationTripleCoefficients_physicalCup (q : ℝ) (n l m h c : ℕ) (r : QuantumCupIndex l m c) :
    occupationTripleCoefficients n l (m+h) c (physicalQuantumCupVector q n l m h c r)=
      quantumCupMonomialAt q n l m h c r :=
  occupationTripleCoefficients_synthesis n l (m+h) c _ (quantumCupMonomialAt_physical_support q n l m h c r)

theorem physicalQuantumCupVector_linearIndependent (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) : LinearIndependent ℝ (physicalQuantumCupVector q n l m h c) := by
  apply LinearIndependent.of_comp (occupationTripleCoefficients n l (m+h) c)
  change LinearIndependent ℝ (fun r =>occupationTripleCoefficients n l (m+h) c (physicalQuantumCupVector q n l m h c r))
  simpa only [occupationTripleCoefficients_physicalCup] using
    quantumCupMonomialAt_linearIndependent q hq n hn l m h c

def physicalQuantumCupSpan (q : ℝ) (n l m h c : ℕ) : Submodule ℝ (quantumOccupationTripleSpace n l (m+h) c) :=
  Submodule.span ℝ (Set.range (physicalQuantumCupVector q n l m h c))

def physicalQuantumCupBasis (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Module.Basis (QuantumCupIndex l m c) ℝ (physicalQuantumCupSpan q n l m h c) :=
  Module.Basis.span (physicalQuantumCupVector_linearIndependent q hq n hn l m h c)

def physicalQuantumCupCoefficientEquiv (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    physicalQuantumCupSpan q n l m h c ≃ₗ[ℝ] quantumCupSpan q n l m h c := by
  let V := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact independentSpanTransport (V:=V) (physicalQuantumCupVector q n l m h c) (quantumCupMonomialAt q n l m h c)
    (physicalQuantumCupVector_linearIndependent q hq n hn l m h c)
    (quantumCupMonomialAt_linearIndependent q hq n hn l m h c) (fun _ =>1) (by intro _;norm_num)

theorem physicalQuantumCupCoefficientEquiv_basis (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    (physicalQuantumCupCoefficientEquiv q hq n hn l m h c (physicalQuantumCupBasis q hq n hn l m h c r)).val=
      quantumCupMonomialAt q n l m h c r := by
  let V := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  have h0:=independentSpanTransport_basis (V:=V) (physicalQuantumCupVector q n l m h c)
    (quantumCupMonomialAt q n l m h c)
    (physicalQuantumCupVector_linearIndependent q hq n hn l m h c)
    (quantumCupMonomialAt_linearIndependent q hq n hn l m h c) (fun _ =>1) (by intro _;norm_num) r
  have hb : physicalQuantumCupBasis q hq n hn l m h c r=
      ⟨physicalQuantumCupVector q n l m h c r,Submodule.subset_span (Set.mem_range_self r)⟩ :=
    Subtype.ext (Module.Basis.span_apply _ r)
  rw [hb]
  simpa only [one_smul] using h0

end AMSPhysical
#print axioms AMSPhysical.physicalQuantumCupVector_linearIndependent
