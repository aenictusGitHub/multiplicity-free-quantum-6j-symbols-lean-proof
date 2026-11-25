import QuantumOccupationShifts
import QuantumTypeAPivotalWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

theorem shiftedOccupation_raising_positive (n r a : ℕ) (k : Fin (n+1))
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : 0<x.val i.succ) :
    0<(shiftedOccupation n r a k x).val i.succ := by
  change 0<x.val i.succ+(Pi.single k (a:ℤ) : Fin (n+1) → ℤ) i.succ
  simp only [Pi.single_apply]
  split_ifs <;> omega

theorem shiftedOccupation_raised (n r a : ℕ) (k : Fin (n+1))
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : 0<x.val i.succ) :
    raisedOccupation n (r+a) (shiftedOccupation n r a k x) i
      (shiftedOccupation_raising_positive n r a k x i hi)=
      shiftedOccupation n r a k (raisedOccupation n r x i hi) := by
  apply Subtype.ext
  change x.val+Pi.single k (a:ℤ)+latticeRoot i.castSucc i.succ=
    x.val+latticeRoot i.castSucc i.succ+Pi.single k (a:ℤ)
  abel

theorem shiftedOccupation_high_E (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a : ℕ)
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : 0<x.val i.succ) :
    typeAFiniteGenerator q hq hD n (r+a) i 0 (quantumOccupationBasis (K:=K) (r+a) (shiftedOccupation n r a 0 x))=
      qInteger q (x.val i.succ) • quantumOccupationBasis (K:=K) (r+a)
        (shiftedOccupation n r a 0 (raisedOccupation n r x i hi)) := by
  have he := typeAFiniteGenerator_E_raised q hq hD n (r+a) (shiftedOccupation n r a 0 x) i
    (shiftedOccupation_raising_positive n r a 0 x i hi)
  rw [shiftedOccupation_high_source,shiftedOccupation_raised] at he
  exact he

theorem shiftedOccupation_high_E_zero (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a : ℕ)
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : x.val i.succ=0) :
    typeAFiniteGenerator q hq hD n (r+a) i 0 (quantumOccupationBasis (K:=K) (r+a) (shiftedOccupation n r a 0 x))=0 := by
  apply typeAFiniteGenerator_E_zero
  rw [shiftedOccupation_high_source,hi]

theorem shiftedOccupation_low_F_raised (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n r b : ℕ)
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : 0<x.val i.succ) :
    typeAFiniteGenerator q hq hD n (r+b) i 1 (quantumOccupationBasis (K:=K) (r+b)
      (shiftedOccupation n r b (Fin.last n) (raisedOccupation n r x i hi)))=
      qInteger q (x.val i.castSucc+1) • quantumOccupationBasis (K:=K) (r+b)
        (shiftedOccupation n r b (Fin.last n) x) := by
  have he := typeAFiniteGenerator_F_reversed q hq hD n (r+b) (shiftedOccupation n r b (Fin.last n) x) i
    (shiftedOccupation_raising_positive n r b (Fin.last n) x i hi)
  rw [shiftedOccupation_raised,shiftedOccupation_low_target] at he
  exact he

theorem shiftedOccupation_low_F_zero (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n r b : ℕ)
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : x.val i.castSucc=0) :
    typeAFiniteGenerator q hq hD n (r+b) i 1
      (quantumOccupationBasis (K:=K) (r+b) (shiftedOccupation n r b (Fin.last n) x))=0 := by
  apply typeAFiniteGenerator_F_zero
  rw [shiftedOccupation_low_target,hi]

theorem shiftedOccupation_low_simpleWeight (n r b : ℕ) (x : occupationWeights (Fin (n+1)) r) (i : Fin n) :
    simpleOccupationWeight n (shiftedOccupation n r b (Fin.last n) x).val i=
      simpleOccupationWeight n x.val i-(b:ℤ)*(if i.succ=Fin.last n then 1 else 0) := by
  unfold simpleOccupationWeight
  rw [shiftedOccupation_low_target]
  change x.val i.castSucc-(x.val i.succ+(Pi.single (Fin.last n) (b:ℤ) : Fin (n+1) → ℤ) i.succ)=_
  simp only [Pi.single_apply]
  by_cases hi : i.succ=Fin.last n <;> simp [hi,eq_comm] <;> ring

end AMSPhysical
#print axioms AMSPhysical.shiftedOccupation_low_F_raised
