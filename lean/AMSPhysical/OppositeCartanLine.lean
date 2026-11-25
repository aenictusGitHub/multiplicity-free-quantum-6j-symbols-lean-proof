import OccupationCartanLine
import QuantumTypeADualSymmetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem opposite_K_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) L)
    (u : Fin (n+1) → ℤ) :
    (typeAOppositeSymmetricRepresentation q hq hD n L (typeAAlgebraGenerator q n i 2) v).val u =
      q^(-simpleOccupationWeight n u i)*v.val u := by
  rw [typeAOpposite_generator]
  change (typeAFiniteGenerator q hq hD n L i 3 v).val u=_
  rw [typeAFiniteGenerator_coe]
  change weightedTranslation (0 : Fin (n+1) → ℤ)
    (fun x => q^(latticePairing (-typeARoot n i) x)) v.val u = _
  rw [weightedTranslation_apply,sub_zero]
  have he : latticePairing (-typeARoot n i) u= -simpleOccupationWeight n u i := by
    simp only [latticePairing,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
    change -latticePairing (latticeRoot i.castSucc i.succ) u=_
    rw [latticePairing_root_left]
    rfl
  rw [he,mul_comm]

theorem opposite_joint_cartan_line (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L)
    (hK : ∀ i : Fin n,typeAOppositeSymmetricRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n L (typeAAlgebraGenerator q n i 2) v =
        q^(-simpleOccupationWeight n x.val i) • v) :
    v=v.val x.val • quantumOccupationBasis (K:=ℝ) L x := by
  apply Subtype.ext
  apply Finsupp.ext
  intro u
  by_cases hu : u=x.val
  · subst u
    simp [quantumOccupationBasis_coe]
  · have hz : v.val u=0 := by
      by_contra hn
      let y : occupationWeights (Fin (n+1)) L:=⟨u,v.property (Finsupp.mem_support_iff.mpr hn)⟩
      have he : simpleOccupationWeight n y.val=simpleOccupationWeight n x.val := by
        funext i
        have hh:=congrArg (fun w : quantumOccupationSpace ℝ (Fin (n+1)) L=>w.val u) (hK i)
        dsimp only at hh
        rw [opposite_K_coefficient] at hh
        change q^(-simpleOccupationWeight n y.val i)*v.val u =
          q^(-simpleOccupationWeight n x.val i)*v.val u at hh
        have hp:=zpow_right_injective₀ hq hq1 (mul_right_cancel₀ hn hh)
        exact neg_injective hp
      have hy:=simpleOccupationWeight_injective n L he
      exact hu (congrArg Subtype.val hy)
    simp [quantumOccupationBasis_coe,Finsupp.single_apply,hu,hz]

theorem occupationAugmentation_opposite_cartan (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L)
    (hK : ∀ i : Fin n,typeAOppositeSymmetricRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n L (typeAAlgebraGenerator q n i 2) v =
        q^(-simpleOccupationWeight n x.val i) • v) :
    occupationAugmentation n L v=v.val x.val := by
  have he:=opposite_joint_cartan_line q hq hq1 n L x v hK
  conv_lhs => rw [he]
  rw [map_smul,occupationAugmentation_basis,smul_eq_mul,mul_one]

end AMSPhysical
#print axioms AMSPhysical.opposite_joint_cartan_line
