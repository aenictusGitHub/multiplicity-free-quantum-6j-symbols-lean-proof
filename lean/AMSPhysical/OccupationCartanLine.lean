import OccupationHighestFunctional

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def occupationAugmentation (n L : ℕ) : quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] ℝ :=
  (quantumOccupationBasis (K:=ℝ) L).constr ℝ (fun _ => 1)

theorem occupationAugmentation_basis (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationAugmentation n L (quantumOccupationBasis (K:=ℝ) L x)=1 := by
  simp [occupationAugmentation]

theorem typeAFiniteGenerator_K_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) L)
    (u : Fin (n+1) → ℤ) :
    (typeAFiniteGenerator q hq hD n L i 2 v).val u =
      q^(simpleOccupationWeight n u i)*v.val u := by
  rw [typeAFiniteGenerator_coe]
  change weightedTranslation (0 : Fin (n+1) → ℤ)
    (fun x => q^(latticePairing (typeARoot n i) x)) v.val u = _
  rw [weightedTranslation_apply,sub_zero]
  simp only [typeARoot,latticePairing_root_left,simpleOccupationWeight,mul_comm]

/-- A joint Cartan weight space of an actual symmetric representation is
one occupation line; this statement is not used for mixed irreps. -/
theorem occupation_joint_cartan_line (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L)
    (hK : ∀ i : Fin n,typeAFiniteGenerator q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n L i 2 v =
        q^(simpleOccupationWeight n x.val i) • v) :
    v=v.val x.val • quantumOccupationBasis (K:=ℝ) L x := by
  apply Subtype.ext
  apply Finsupp.ext
  intro u
  by_cases hu : u=x.val
  · subst u
    simp [quantumOccupationBasis_coe]
  · have hz : v.val u=0 := by
      by_contra hn
      let y : occupationWeights (Fin (n+1)) L :=
        ⟨u,v.property (Finsupp.mem_support_iff.mpr hn)⟩
      have he : (fun i : Fin n=>q^(simpleOccupationWeight n y.val i)) =
          (fun i : Fin n=>q^(simpleOccupationWeight n x.val i)) := by
        funext i
        have hh:=congrArg (fun w : quantumOccupationSpace ℝ (Fin (n+1)) L=>w.val u) (hK i)
        dsimp only at hh
        rw [typeAFiniteGenerator_K_coefficient] at hh
        change q^(simpleOccupationWeight n y.val i)*v.val u =
          q^(simpleOccupationWeight n x.val i)*v.val u at hh
        exact mul_right_cancel₀ hn hh
      have hy:=typeA_toral_eigenvalues_injective q hq hq1 n L he
      exact hu (congrArg Subtype.val hy)
    simp [quantumOccupationBasis_coe,Finsupp.single_apply,hu,hz]

theorem occupationAugmentation_joint_cartan (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L)
    (hK : ∀ i : Fin n,typeAFiniteGenerator q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n L i 2 v =
        q^(simpleOccupationWeight n x.val i) • v) :
    occupationAugmentation n L v=v.val x.val := by
  have he:=occupation_joint_cartan_line q hq hq1 n L x v hK
  conv_lhs => rw [he]
  rw [map_smul,occupationAugmentation_basis,smul_eq_mul,mul_one]

end AMSPhysical
#print axioms AMSPhysical.occupation_joint_cartan_line
