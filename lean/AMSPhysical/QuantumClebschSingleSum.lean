import QuantumCoupledExpansion
import TensorCoefficientCollapse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module

def clebschSingleTerm (q : ℝ) (l m : ℤ) (r a k t : ℕ) : ℝ :=
  couplingCoefficient q m r k*gaussianBinomial (q^2) a t*q^(-(t:ℤ)*(l-2*(k:ℤ)))*
    qFalling q (l-(k:ℤ)) (a-t)*qFalling q (m-(r:ℤ)+(k:ℤ)) t

def clebschSingleSum (q : ℝ) (l m : ℤ) (r a : ℕ) (u : ℤ) : ℝ :=
  ∑ k∈Finset.range (r+1),if DescendantAdmissible a k u then
    clebschSingleTerm q l m r a k (descendantIndex a k u) else 0

theorem quantumCoupledExpansion_coefficient (q : ℝ) (l m : ℤ) (r a : ℕ) (u v : ℤ)
    (huv : u+v=(r:ℤ)+(a:ℤ)) :
    tensorCoefficient u v (quantumCoupledExpansion q l m r a)=clebschSingleSum q l m r a u := by
  unfold quantumCoupledExpansion clebschSingleSum clebschSingleTerm
  exact tensorCoefficient_double_collapse r a u v huv _

/-- Coefficient in the standard weight bases of the independently constructed isometric CG map. -/
def standardClebschCoefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (u v : ℤ) : ℝ :=
  tensorCoefficient u v (finiteTensorForget l m
    (unitaryQuantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) a)))

theorem standardClebschCoefficient_singleSum (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (u v : ℤ)
    (huv : u+v=(r.val:ℤ)+(a.val:ℤ)) :
    standardClebschCoefficient q hq hq1 l m r a u v=
      ((Real.sqrt (couplingNormClosed q (l-r.val) (m-r.val) r.val))⁻¹*
        (qFalling q (coupledLabel l m r) a.val)⁻¹)*clebschSingleSum q l m r.val a.val u := by
  unfold standardClebschCoefficient
  rw [unitaryQuantumClebschMap_closed_expansion,map_smul,smul_eq_mul,quantumCoupledExpansion_coefficient q _ _ _ _ u v huv]

end AMSPhysical

#print axioms AMSPhysical.standardClebschCoefficient_singleSum
