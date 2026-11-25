import PhysicalTypeIFirstBoundarySigns
import QuantumTripleCreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem occupationTripleCoefficients_nonnegative (n l m c : ℕ) (v : quantumOccupationTripleSpace n l m c) :
    CoefficientSupported (tripleOccupationNonnegative n) (occupationTripleCoefficients n l m c v) := by
  intro p hp
  have hs:=occupationTripleCoefficients_support n l m c v p hp
  exact ⟨hs.1.1,hs.2.1.1,hs.2.2.1⟩

theorem physicalTypeIFirstBoundary_left_creation (q : ℝ) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) :
    physicalTypeIFirstBoundary n (l+1) (m+1) 0 c (finiteTripleLeftCreation q n l m c v) =
      q^(-(l:ℤ)-(m:ℤ))*physicalTypeIFirstBoundary n l m 0 c v := by
  change occupationTripleCoefficients n (l+1) ((m+1)+0) c (finiteTripleLeftCreation q n l m c v)
    (cupFirstBoundaryPoint n (l+1) 0 c (m+1) 0) = _
  rw [occupationTripleCoefficients_leftCreation]
  have hp : cupFirstBoundaryPoint n (l+1) 0 c (m+1) 0 =
      (Pi.single 0 ((l:ℤ)+1),Pi.single 0 (m:ℤ)+Pi.single 0 1,Pi.single 0 (c:ℤ)) := by
    ext i <;> simp [cupFirstBoundaryPoint,Pi.single_apply] <;> split_ifs <;> push_cast <;> ring
  rw [hp,tripleLeftCreation_first_boundary q n (l:ℤ) _
    (occupationTripleCoefficients_nonnegative n l m c v)]
  simp only [Pi.single_eq_same]
  congr 1
  simp only [physicalTypeIFirstBoundary,LinearMap.comp_apply,Finsupp.lapply_apply,
    cupFirstBoundaryPoint,Nat.add_zero,Nat.cast_zero,add_zero,Pi.single_zero,zero_add]

theorem physicalTypeIFirstBoundary_right_creation (q : ℝ) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) :
    physicalTypeIFirstBoundary n l (m+1) 0 (c+1) (finiteTripleRightCreation q n l m c v) =
      ((-1:ℝ)^n*q^(-(n:ℤ)-(m:ℤ)-(c:ℤ)))*physicalTypeIFirstBoundary n l m 0 c v := by
  change occupationTripleCoefficients n l ((m+1)+0) (c+1) (finiteTripleRightCreation q n l m c v)
    (cupFirstBoundaryPoint n l 0 (c+1) (m+1) 0) = _
  rw [occupationTripleCoefficients_rightCreation]
  have hp : cupFirstBoundaryPoint n l 0 (c+1) (m+1) 0 =
      (Pi.single 0 (l:ℤ),Pi.single 0 (m:ℤ)+Pi.single 0 1,Pi.single 0 ((c:ℤ)+1)) := by
    ext i <;> simp [cupFirstBoundaryPoint,Pi.single_apply] <;> split_ifs <;> push_cast <;> ring
  rw [hp,tripleRightCreation_third_first_boundary q n (c:ℤ) _
    (occupationTripleCoefficients_nonnegative n l m c v)]
  simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  congr 1
  simp only [physicalTypeIFirstBoundary,LinearMap.comp_apply,Finsupp.lapply_apply,
    cupFirstBoundaryPoint,Nat.add_zero,Nat.cast_zero,add_zero,Pi.single_zero,zero_add]

theorem typeIFirstBoundarySign_left_step (n m t : ℕ) (_ht : t≤m) :
    typeIFirstBoundarySign n (m+1) (t+1)=(-1:ℝ)^(n-1)*typeIFirstBoundarySign n m t := by
  simp only [typeIFirstBoundarySign,quantumCupRankGauge,Nat.add_sub_add_right,Nat.mul_add,Nat.mul_one,pow_add]
  ring

theorem typeIFirstBoundarySign_right_step (n m t : ℕ) (hn : 0<n) (ht : t≤m) :
    typeIFirstBoundarySign n (m+1) t=(-1:ℝ)^n*typeIFirstBoundarySign n m t := by
  have hm : m+1-t=(m-t)+1 := by omega
  have hn' : n=(n-1)+1 := by omega
  have hp : (-1:ℝ)^n=(-1:ℝ)^(n-1)*(-1) := by
    conv_lhs => rw [hn',pow_add,pow_one]
  simp only [typeIFirstBoundarySign,quantumCupRankGauge,hm,Nat.mul_add,Nat.mul_one,pow_add,pow_one]
  rw [hp]
  ring

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIFirstBoundary_left_creation
#print axioms AMSPhysical.physicalTypeIFirstBoundary_right_creation
