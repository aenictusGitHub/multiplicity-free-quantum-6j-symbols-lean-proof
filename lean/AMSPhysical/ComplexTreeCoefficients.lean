import ComplexClebschAnalytic
import QuantumTreeBasisCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def complexCouplingCoefficient (q:ℂ) (m:ℤ) (r k:ℕ):ℂ:=
  (-1:ℂ)^k*q^(couplingExponent m r k)*complexQfactorial q r/
    (complexQfactorial q k*complexQfactorial q (r-k))

theorem complexCouplingCoefficient_ofReal (q:ℝ) (hq:0<q) (hq1:q≠1) (m:ℤ) (r k:ℕ) (hk:k≤r):
    complexCouplingCoefficient (q:ℂ) m r k=((couplingCoefficient q m r k:ℝ):ℂ):=by
  rw [couplingCoefficient_factorial q hq hq1 m r k hk]
  simp only [complexCouplingCoefficient,complexQfactorial_ofReal,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_zpow,Complex.ofReal_neg,Complex.ofReal_one]

/-- Independent complete coordinates of the standard left CG tree. -/
def complexLeftTreeCoefficient (q:ℂ) (l m n:ℕ) (p:LeftHighestPath l m n)
    (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):ℂ:=
  (complexPositiveRoot (complexCouplingNormClosed q
    (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val))⁻¹*
    ∑ t:Fin (p.2.val+1),complexCouplingCoefficient q (n:ℤ) p.2.val t.val*
      complexClebschCoefficient q l m p.1.val (leftRootIndexPair l m n p t).1.val i.val j.val*
      (if (leftRootIndexPair l m n p t).2=k then 1 else 0)

/-- Independent complete coordinates of the standard right CG tree. -/
def complexRightTreeCoefficient (q:ℂ) (l m n:ℕ) (p:RightHighestPath l m n)
    (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):ℂ:=
  (complexPositiveRoot (complexCouplingNormClosed q
    (l-p.2.val) (coupledLabel m n p.1-p.2.val) p.2.val))⁻¹*
    ∑ t:Fin (p.2.val+1),complexCouplingCoefficient q (coupledLabel m n p.1:ℤ) p.2.val t.val*
      (if (rightRootIndexPair l m n p t).1=i then 1 else 0)*
      complexClebschCoefficient q m n p.1.val (rightRootIndexPair l m n p t).2.val j.val k.val

theorem complexLeftTreeCoefficient_ofReal_actual (q:ℝ) (hq:0<q) (hq1:q≠1) (l m n:ℕ)
    (p:LeftHighestPath l m n) (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):
    complexLeftTreeCoefficient (q:ℂ) l m n p i j k=
      ((((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
        (standardWeightBasis (K:=ℝ) n)).repr
        (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2) ((i,j),k):ℂ):=by
  rw [quantumLeftTreeHighest_basis_coefficient,quantumHighestNorm_closed q hq hq1]
  unfold complexLeftTreeCoefficient
  rw [complexCouplingNormClosed_ofReal,
    complexPositiveRoot_ofReal _ (couplingNormClosed_pos q hq _ _ _)]
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [complexCouplingCoefficient_ofReal q hq hq1 _ _ _ (by have h:=t.isLt;omega),
    complexClebschCoefficient_ofReal_actual q hq hq1 l m p.1 (leftRootIndexPair l m n p t).1 i j]
  split_ifs <;> simp only [Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_zero]

theorem complexRightTreeCoefficient_ofReal_actual (q:ℝ) (hq:0<q) (hq1:q≠1) (l m n:ℕ)
    (p:RightHighestPath l m n) (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):
    complexRightTreeCoefficient (q:ℂ) l m n p i j k=
      ((((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
        (standardWeightBasis (K:=ℝ) n)).repr
        (quantumRightTreeHighest q hq hq1 l m n p.1 p.2) ((i,j),k):ℂ):=by
  rw [quantumRightTreeHighest_basis_coefficient,quantumHighestNorm_closed q hq hq1]
  unfold complexRightTreeCoefficient
  rw [complexCouplingNormClosed_ofReal,
    complexPositiveRoot_ofReal _ (couplingNormClosed_pos q hq _ _ _)]
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [complexCouplingCoefficient_ofReal q hq hq1 _ _ _ (by have h:=t.isLt;omega),
    complexClebschCoefficient_ofReal_actual q hq hq1 m n p.1 (rightRootIndexPair l m n p t).2 j k]
  split_ifs <;> simp only [Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_zero]

end AMSPhysical
#print axioms AMSPhysical.complexLeftTreeCoefficient_ofReal_actual
#print axioms AMSPhysical.complexRightTreeCoefficient_ofReal_actual
