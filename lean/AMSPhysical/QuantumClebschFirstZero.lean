import QuantumClebschSingleSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

theorem clebschSingleSum_first_zero (q : ℝ) (l m : ℤ) (r a : ℕ) :
    clebschSingleSum q l m r a 0=q^(-(a:ℤ)*l)*qFalling q (m-(r:ℤ)) a := by
  classical
  unfold clebschSingleSum
  rw [Finset.sum_eq_single 0]
  · have ha : DescendantAdmissible a 0 0 := by unfold DescendantAdmissible;constructor <;> omega
    have hi : descendantIndex a 0 0=a := by unfold descendantIndex;omega
    rw [if_pos ha,hi]
    unfold clebschSingleTerm
    simp only [couplingCoefficient,gaussianBinomial_self,Nat.sub_self,qFalling,Nat.cast_zero,
      mul_zero,sub_zero,add_zero,one_mul,mul_one]
  · intro k hk hk0
    have ha : ¬DescendantAdmissible a k 0 := by intro h;have hh := h.2;omega
    rw [if_neg ha]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem standardClebschCoefficient_weight_mismatch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (u v : ℤ)
    (huv : u+v≠(r.val:ℤ)+(a.val:ℤ)) : standardClebschCoefficient q hq hq1 l m r a u v=0 := by
  unfold standardClebschCoefficient
  rw [unitaryQuantumClebschMap_closed_expansion,map_smul,smul_eq_mul]
  unfold quantumCoupledExpansion
  rw [tensorCoefficient_double_weight_mismatch r.val a.val u v huv,mul_zero]

theorem standardClebschCoefficient_first_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (v : ℤ) :
    standardClebschCoefficient q hq hq1 l m r a 0 v=
      if v=(r.val:ℤ)+(a.val:ℤ) then
        (Real.sqrt (couplingNormClosed q (l-r.val) (m-r.val) r.val))⁻¹*
          (qFalling q (coupledLabel l m r) a.val)⁻¹*q^(-(a.val:ℤ)*(l:ℤ))*
            qFalling q ((m:ℤ)-(r.val:ℤ)) a.val else 0 := by
  by_cases hv : v=(r.val:ℤ)+(a.val:ℤ)
  · rw [if_pos hv,standardClebschCoefficient_singleSum q hq hq1 l m r a 0 v (by omega),
      clebschSingleSum_first_zero]
    ring
  · rw [if_neg hv]
    exact standardClebschCoefficient_weight_mismatch q hq hq1 l m r a 0 v (by omega)

end AMSPhysical

#print axioms AMSPhysical.standardClebschCoefficient_first_zero
