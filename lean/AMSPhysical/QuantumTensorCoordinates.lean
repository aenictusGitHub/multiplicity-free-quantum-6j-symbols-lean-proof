import QuantumProjectedCoordinates
import QuantumIntermediateCasimir

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem weightShift_coefficient (s : ℤ) (w : ℤ → ℝ) (k : ℤ) (p : WeightModule ℝ) :
    weightShift s w p k=w (k-s)*p (k-s) := by
  have he : (Finsupp.lapply k).comp (weightShift s w)=
      w (k-s) • (Finsupp.lapply (k-s) : WeightModule ℝ →ₗ[ℝ] ℝ) := by
    apply Finsupp.lhom_ext
    intro a c
    simp only [LinearMap.comp_apply,weightShift_single,LinearMap.smul_apply,Finsupp.lapply_apply,smul_eq_mul]
    by_cases ha : a=k-s
    · subst a
      simp only [sub_add_cancel,Finsupp.single_eq_same]
      ring
    · have hne : a+s≠k := by omega
      simp only [Finsupp.single_apply,if_neg ha,if_neg hne,mul_zero]
  exact DFunLike.congr_fun he p

theorem tensorCoefficient_shift_map (s t : ℤ) (w z : ℤ → ℝ) (y v : ℤ)
    (p : WeightModule ℝ ⊗[ℝ] WeightModule ℝ) :
    tensorCoefficient y v (TensorProduct.map (weightShift s w) (weightShift t z) p)=
      w (y-s)*z (v-t)*tensorCoefficient (y-s) (v-t) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero,mul_zero]
  | tmul a b =>
    rw [TensorProduct.map_tmul,tensorCoefficient_tmul,tensorCoefficient_tmul,
      weightShift_coefficient,weightShift_coefficient]
    ring
  | add a b ha hb => simp only [map_add,ha,hb,mul_add]

theorem tensorCoefficient_map_left (s : ℤ) (w : ℤ → ℝ) (y v : ℤ)
    (p : WeightModule ℝ ⊗[ℝ] WeightModule ℝ) :
    tensorCoefficient y v (TensorProduct.map (weightShift s w) 1 p)=
      w (y-s)*tensorCoefficient (y-s) v p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero,mul_zero]
  | tmul a b =>
    rw [TensorProduct.map_tmul,Module.End.one_apply,tensorCoefficient_tmul,tensorCoefficient_tmul,
      weightShift_coefficient]
    ring
  | add a b ha hb => simp only [map_add,ha,hb,mul_add]

theorem tensorCoefficient_map_right (s : ℤ) (w : ℤ → ℝ) (y v : ℤ)
    (p : WeightModule ℝ ⊗[ℝ] WeightModule ℝ) :
    tensorCoefficient y v (TensorProduct.map (1 : Module.End ℝ (WeightModule ℝ)) (weightShift s w) p)=
      w (v-s)*tensorCoefficient y (v-s) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero,mul_zero]
  | tmul a b =>
    rw [TensorProduct.map_tmul,Module.End.one_apply,tensorCoefficient_tmul,tensorCoefficient_tmul,
      weightShift_coefficient]
    ring
  | add a b ha hb => simp only [map_add,ha,hb,mul_add]

/-- Exact finite tensor generator coefficients, obtained through the proved inclusion. -/
theorem finiteTensor_E_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) :
    finiteTensorCoefficient l m y z
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 0) p)=
      qInteger q (y+1)*q^((m:ℤ)-2*z)*finiteTensorCoefficient l m (y+1) z p+
        qInteger q (z+1)*finiteTensorCoefficient l m y (z+1) p := by
  have he := finiteTensorForget_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
    (uqGenerator q 0) p
  have hg (L : ℤ) (i : Fin 4) : quantumRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q i)=
      ![quantumE q,quantumF q L,quantumK q L,quantumKinv q L] i :=
    quantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L i
  unfold finiteTensorCoefficient
  simp only [LinearMap.comp_apply]
  rw [← he,tensorRepresentation_E_end (V:=WeightModule ℝ) (W:=WeightModule ℝ),hg (l:ℤ) 0,hg (m:ℤ) 2,hg (m:ℤ) 0]
  change tensorCoefficient y z (((TensorProduct.map (quantumE q) (quantumK q (m:ℤ))+
    TensorProduct.map (1 : Module.End ℝ (WeightModule ℝ)) (quantumE q)) :
      Module.End ℝ (WeightModule ℝ ⊗[ℝ] WeightModule ℝ)) (finiteTensorForget l m p))=_
  simp only [LinearMap.add_apply,map_add,quantumE,quantumK,tensorCoefficient_shift_map,
    tensorCoefficient_map_right,sub_neg_eq_add,sub_zero]

theorem finiteTensor_F_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) :
    finiteTensorCoefficient l m y z
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 1) p)=
      qInteger q ((l:ℤ)-y+1)*finiteTensorCoefficient l m (y-1) z p+
        q^(-(l:ℤ)+2*y)*qInteger q ((m:ℤ)-z+1)*finiteTensorCoefficient l m y (z-1) p := by
  have he := finiteTensorForget_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
    (uqGenerator q 1) p
  unfold finiteTensorCoefficient
  simp only [LinearMap.comp_apply]
  rw [← he,infiniteTensor_F_end]
  unfold tensorQuantumF quantumF quantumKinv
  simp only [LinearMap.add_apply,map_add,tensorCoefficient_shift_map,tensorCoefficient_map_left,sub_zero]
  have h₁ : (l:ℤ)-(y-1)=(l:ℤ)-y+1 := by omega
  have h₂ : (m:ℤ)-(z-1)=(m:ℤ)-z+1 := by omega
  have h₃ : -((l:ℤ)-2*y)=-(l:ℤ)+2*y := by omega
  rw [h₁,h₂,h₃]

theorem finiteTensor_K_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) :
    finiteTensorCoefficient l m y z
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 2) p)=
      q^((l:ℤ)+(m:ℤ)-2*(y+z))*finiteTensorCoefficient l m y z p := by
  have he := finiteTensorForget_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
    (uqGenerator q 2) p
  have hg (L : ℤ) (i : Fin 4) : quantumRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q i)=
      ![quantumE q,quantumF q L,quantumK q L,quantumKinv q L] i :=
    quantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L i
  unfold finiteTensorCoefficient
  simp only [LinearMap.comp_apply]
  rw [← he,tensorRepresentation_K_end (V:=WeightModule ℝ) (W:=WeightModule ℝ),hg (l:ℤ) 2,hg (m:ℤ) 2]
  change tensorCoefficient y z (TensorProduct.map (quantumK q (l:ℤ)) (quantumK q (m:ℤ))
    (finiteTensorForget l m p))=_
  simp only [quantumK,tensorCoefficient_shift_map,sub_zero]
  rw [← zpow_add₀ (ne_of_gt hq)]
  congr 2
  omega

theorem finiteTensor_Ki_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) :
    finiteTensorCoefficient l m y z
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 3) p)=
      q^(-((l:ℤ)+(m:ℤ)-2*(y+z)))*finiteTensorCoefficient l m y z p := by
  have he := finiteTensorForget_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
    (uqGenerator q 3) p
  have hg (L : ℤ) (i : Fin 4) : quantumRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q i)=
      ![quantumE q,quantumF q L,quantumK q L,quantumKinv q L] i :=
    quantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L i
  unfold finiteTensorCoefficient
  simp only [LinearMap.comp_apply]
  rw [← he,tensorRepresentation_Ki_end (V:=WeightModule ℝ) (W:=WeightModule ℝ),hg (l:ℤ) 3,hg (m:ℤ) 3]
  change tensorCoefficient y z (TensorProduct.map (quantumKinv q (l:ℤ)) (quantumKinv q (m:ℤ))
    (finiteTensorForget l m p))=_
  simp only [quantumKinv,tensorCoefficient_shift_map,sub_zero]
  rw [← zpow_add₀ (ne_of_gt hq)]
  congr 2
  omega

end AMSPhysical

#print axioms AMSPhysical.finiteTensor_E_coefficient
#print axioms AMSPhysical.finiteTensor_F_coefficient
