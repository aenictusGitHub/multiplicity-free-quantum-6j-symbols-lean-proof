import QuantumClebschIsometry
import QuantumClebschFirstFormula
import QuantumPhysicalTripleInstances
import QuantumTripleMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Independent standard isometric Clebsch map with an explicitly fixed
output label. This permits different determinant backgrounds on its two
pair realizations. -/
def standardClebschAtLabel (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L) :
    finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) := by
  subst L
  exact unitaryQuantumClebschMap q hq hq1 l m r

theorem standardClebschAtLabel_isometry (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L) (v w:finiteWeightSpace (K:=ℝ) L) :
    quantumTensorBilin q l m (standardClebschAtLabel q hq hq1 l m r L hL v)
      (standardClebschAtLabel q hq hq1 l m r L hL w)=quantumPair q L v w := by
  subst L
  exact unitaryQuantumClebschMap_isometry q hq hq1 l m r v w

theorem standardClebschAtLabel_intertwines (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L) :
    IsQuantumIntertwiner q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L)
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
      (standardClebschAtLabel q hq hq1 l m r L hL) := by
  subst L
  exact unitaryQuantumClebschMap_intertwines q hq hq1 l m r

end AMSPhysical
#print axioms AMSPhysical.standardClebschAtLabel_intertwines
