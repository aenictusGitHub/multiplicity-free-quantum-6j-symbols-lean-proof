import PhysicalTypeILeftCreationGeometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeILeftCreationScale (q : ℝ) (n l m c : ℕ) (t : QuantumCupIndex l m c) : ℝ :=
  Real.sqrt (mixedCreationSpectralScalar q n l m (physicalTypeILeftIndex l m 0 c t).val)

theorem typeILeftCreationScale_pos (q : ℝ) (hq : 0<q) (n l m c : ℕ) (t : QuantumCupIndex l m c) :
    0 < typeILeftCreationScale q n l m c t :=
  Real.sqrt_pos.mpr (mixedCreationSpectralScalar_pos q hq n l m _)

def typeILeftCreatedUnit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :=
  ((-1:ℝ)^(n-1)*(typeILeftCreationScale q n l m c t)⁻¹) •
    physicalTypeIHighestLeftCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c
      (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t)

theorem typeILeftCreatedUnit_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    typeILeftCreatedUnit q hq hq1 n hn l m c hadm t ∈
      physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        n (l+1) (m+1) 0 c (cupCreateLeftIndex l m c t) := by
  change (typeILeftCreatedUnit q hq hq1 n hn l m c hadm t).val∈physicalTripleLeftChannelGeneral
    q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) c _
  apply Submodule.smul_mem
  exact finiteTripleLeftCreation_mem_successor q hq hq1 n hn l m c t _
    (physicalTypeILeftCoupling_mem_channel q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t)

theorem typeILeftCreatedUnit_norm_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    physicalTripleBilin q n (l+1) ((m+1)+0) c
      (typeILeftCreatedUnit q hq hq1 n hn l m c hadm t).val
      (typeILeftCreatedUnit q hq hq1 n hn l m c hadm t).val=1 := by
  unfold typeILeftCreatedUnit
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul,Nat.add_zero]
  change ((-1:ℝ)^(n-1)*(typeILeftCreationScale q n l m c t)⁻¹) *
    (((-1:ℝ)^(n-1)*(typeILeftCreationScale q n l m c t)⁻¹) *
      physicalTripleBilin q n (l+1) (m+1) c
        (finiteTripleLeftCreation q n l m c
          (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val)
        (finiteTripleLeftCreation q n l m c
          (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val))=1
  have hm : (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val ∈
      physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        n l m c (physicalTypeILeftIndex l m 0 c t) :=
    physicalTypeILeftCoupling_mem_channel q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t
  have hg:=finiteTripleLeftCreation_gram_channel q hq hq1 n hn l m c
    (physicalTypeILeftIndex l m 0 c t)
    (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val
    (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val hm hm
  have hu:=physicalTypeILeftCoupling_unit q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t
  simp only [Nat.add_zero] at hu
  rw [hg,hu,mul_one]
  have hs:=Real.sq_sqrt (mixedCreationSpectralScalar_pos q hq n l m (physicalTypeILeftIndex l m 0 c t).val).le
  have hnz:=ne_of_gt (typeILeftCreationScale_pos q hq n l m c t)
  change (typeILeftCreationScale q n l m c t)^2=_ at hs
  have hsg : (-1:ℝ)^(n-1)*(-1:ℝ)^(n-1)=1 := by rw [← mul_pow];norm_num
  rw [← hs]
  calc
    _ = ((-1:ℝ)^(n-1)*(-1:ℝ)^(n-1))*
      ((typeILeftCreationScale q n l m c t)⁻¹*(typeILeftCreationScale q n l m c t)⁻¹*
        (typeILeftCreationScale q n l m c t)^2) := by ring
    _ = 1 := by rw [hsg];field_simp

theorem typeILeftCreatedUnit_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    0 < typeIFirstBoundarySign n (m+1) (cupCreateLeftIndex l m c t).val.val *
      physicalTypeIFirstBoundary n (l+1) (m+1) 0 c
        (typeILeftCreatedUnit q hq hq1 n hn l m c hadm t).val := by
  have ht:=t.val.isLt
  change 0 < typeIFirstBoundarySign n (m+1) (t.val.val+1) * _
  rw [typeIFirstBoundarySign_left_step n m t.val.val (by omega)]
  unfold typeILeftCreatedUnit
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul]
  change 0 < ((-1:ℝ)^(n-1)*typeIFirstBoundarySign n m t.val.val)*
    (((-1:ℝ)^(n-1)*(typeILeftCreationScale q n l m c t)⁻¹)*
      physicalTypeIFirstBoundary n (l+1) (m+1) 0 c
        (finiteTripleLeftCreation q n l m c
          (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val))
  rw [physicalTypeIFirstBoundary_left_creation]
  have hsq : (-1:ℝ)^(n-1)*(-1:ℝ)^(n-1)=1 := by rw [← mul_pow];norm_num
  have he : ((-1:ℝ)^(n-1)*typeIFirstBoundarySign n m t.val.val)*
      (((-1:ℝ)^(n-1)*(typeILeftCreationScale q n l m c t)⁻¹)*
        (q^(-(l:ℤ)-(m:ℤ))*physicalTypeIFirstBoundary n l m 0 c
          (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val)) =
      ((-1:ℝ)^(n-1)*(-1:ℝ)^(n-1))*((typeILeftCreationScale q n l m c t)⁻¹*q^(-(l:ℤ)-(m:ℤ)))*
        (typeIFirstBoundarySign n m t.val.val*physicalTypeIFirstBoundary n l m 0 c
          (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val) := by ring
  rw [he,hsq,one_mul]
  exact mul_pos
    (mul_pos (inv_pos.mpr (typeILeftCreationScale_pos q hq n l m c t)) (zpow_pos hq _))
    (physicalTypeILeftCoupling_first_boundary_signed_pos q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t)

/-- The Type-I left contraction step has the universal incident-vertex
phase (-1)^(N-2), with a strictly positive normalization. -/
theorem physicalTypeILeftCoupling_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    finiteTripleLeftCreation q n l m c
      (physicalTypeILeftCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val =
      ((-1:ℝ)^(n-1)*typeILeftCreationScale q n l m c t) •
        (physicalTypeILeftCoupling q hq hq1 n hn (l+1) (m+1) 0 c (by omega) (Or.inl rfl)
          (cupCreateLeftIndex l m c t)).val := by
  have hu:=physicalTypeILeftCoupling_unique_boundary q hq hq1 n hn (l+1) (m+1) 0 c
    (by omega) (Or.inl rfl) (cupCreateLeftIndex l m c t)
    (typeILeftCreatedUnit q hq hq1 n hn l m c hadm t)
    (typeILeftCreatedUnit_mem q hq hq1 n hn l m c hadm t)
    (typeILeftCreatedUnit_norm_one q hq hq1 n hn l m c hadm t)
    (typeILeftCreatedUnit_boundary q hq hq1 n hn l m c hadm t)
  have hz:=ne_of_gt (typeILeftCreationScale_pos q hq n l m c t)
  have hsq : (-1:ℝ)^(n-1)*(-1:ℝ)^(n-1)=1 := by rw [← mul_pow];norm_num
  calc
    _ = ((-1:ℝ)^(n-1)*typeILeftCreationScale q n l m c t) •
      (typeILeftCreatedUnit q hq hq1 n hn l m c hadm t).val := by
        unfold typeILeftCreatedUnit
        simp only [Submodule.coe_smul_of_tower,physicalTypeIHighestLeftCreation_val,smul_smul]
        have he : ((-1:ℝ)^(n-1)*typeILeftCreationScale q n l m c t)*
            ((-1:ℝ)^(n-1)*(typeILeftCreationScale q n l m c t)⁻¹)=1 := by
          calc
            _ = ((-1:ℝ)^(n-1)*(-1:ℝ)^(n-1))*
              (typeILeftCreationScale q n l m c t*(typeILeftCreationScale q n l m c t)⁻¹) := by ring
            _ = 1 := by rw [hsq,mul_inv_cancel₀ hz,mul_one]
        rw [he,one_smul]
    _ = _ := by rw [hu]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeILeftCoupling_creation
