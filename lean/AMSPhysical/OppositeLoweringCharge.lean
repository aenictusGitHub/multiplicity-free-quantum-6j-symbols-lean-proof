import OccupationHighestFunctional

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def loweringOccupationShift (n : ℕ) (w : List (Fin n)) : Fin (n+1) → ℤ :=
  (w.map (fun i => latticeRoot i.castSucc i.succ)).sum

def loweringZeroCharge (n : ℕ) (w : List (Fin n)) : ℤ :=
  (w.map (fun i => if i.castSucc=0 then (1:ℤ) else 0)).sum

theorem loweringOccupationShift_zero (n : ℕ) (w : List (Fin n)) :
    loweringOccupationShift n w 0=loweringZeroCharge n w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hi : i.succ≠(0:Fin (n+1)) := by intro he;have h:=congrArg Fin.val he;simp at h
    simp only [loweringOccupationShift,loweringZeroCharge,List.map_cons,List.sum_cons,Pi.add_apply,
      latticeRoot,Pi.sub_apply,Pi.single_apply,if_neg hi,if_neg (Ne.symm hi),sub_zero]
    change (if 0=i.castSucc then (1:ℤ) else 0)+loweringOccupationShift n w 0 = _
    rw [ih]
    simp only [eq_comm]
    rfl

/-- A lowering word in the opposite symmetric module has a single literal
occupation path, possibly with zero coefficient at a physical boundary. -/
theorem oppositeLowered_single (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n s : ℕ) (w : List (Fin n)) :
    ∃ a : ℝ,
      (typeALoweredVector q n (typeAOppositeSymmetricRepresentation q hq hD n s)
        (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w).val =
        Finsupp.single ((lowestOccupation n s).val+loweringOccupationShift n w) a := by
  induction w with
  | nil => refine ⟨1,?_⟩;simp only [typeALoweredVector_nil,quantumOccupationBasis_coe,loweringOccupationShift,
      List.map_nil,List.sum_nil,add_zero]
  | cons i w ih =>
    obtain ⟨a,ha⟩:=ih
    refine ⟨a*qInteger q (((lowestOccupation n s).val+loweringOccupationShift n w) i.succ),?_⟩
    rw [typeALoweredVector_cons,typeAOpposite_generator]
    change (typeAFiniteGenerator q hq hD n s i 0 _).val = _
    rw [typeAFiniteGenerator_coe]
    change quantumLatticeMove q i.castSucc i.succ _ = _
    rw [ha,quantumLatticeMove_single]
    congr 1
    simp only [loweringOccupationShift,List.map_cons,List.sum_cons]
    abel

theorem oppositeLowered_first_nonzero_charge (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (s : ℕ) (w : List (Fin n))
    (hc : occupationHighestFunctional n s
      (typeALoweredVector q n (typeAOppositeSymmetricRepresentation q hq hD n s)
        (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w)≠0) :
    loweringZeroCharge n w=(s:ℤ) := by
  obtain ⟨a,ha⟩:=oppositeLowered_single q hq hD n s w
  change (typeALoweredVector q n (typeAOppositeSymmetricRepresentation q hq hD n s)
    (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w).val (highestOccupation n s).val≠0 at hc
  rw [ha,Finsupp.single_apply] at hc
  have hi : (lowestOccupation n s).val+loweringOccupationShift n w=(highestOccupation n s).val := by
    by_contra h
    rw [if_neg h] at hc
    exact hc rfl
  have hz:=congrFun hi (0:Fin (n+1))
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro h;have he:=congrArg Fin.val h;simp at he;omega
  simp only [Pi.add_apply,loweringOccupationShift_zero,lowestOccupation,highestOccupation,Pi.single_apply,
    if_neg hn0,if_neg (Ne.symm hn0),if_pos rfl,zero_add] at hz
  exact hz

theorem loweringZeroCharge_product (q : ℝ) (hq : q≠0) (n p : ℕ) (w : List (Fin n)) :
    (w.map (fun i => q^(-(p:ℤ)*(if i.castSucc=0 then 1 else 0)))).prod =
      q^(-(p:ℤ)*loweringZeroCharge n w) := by
  induction w with
  | nil => simp [loweringZeroCharge]
  | cons i w ih =>
    simp only [List.map_cons,List.prod_cons,loweringZeroCharge,List.sum_cons] at *
    rw [ih,← zpow_add₀ hq]
    congr 1
    ring

end AMSPhysical
#print axioms AMSPhysical.oppositeLowered_first_nonzero_charge
