import PhysicalTypeIRightCreationGeometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeIRightCreationScale (q : ℝ) (n l m c : ℕ) (t : QuantumCupIndex l m c) : ℝ :=
  Real.sqrt (mixedCreationSpectralScalar q n m c (physicalTypeIRightIndex l m 0 c t).val)

theorem typeIRightCreationScale_pos (q : ℝ) (hq : 0<q) (n l m c : ℕ) (t : QuantumCupIndex l m c) :
    0 < typeIRightCreationScale q n l m c t :=
  Real.sqrt_pos.mpr (mixedCreationSpectralScalar_pos q hq n m c _)

def typeIRightCreatedUnit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :=
  (typeIRightCreationScale q n l m c t)⁻¹ •
    physicalTypeIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c
      (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t)

theorem typeIRightCreatedUnit_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    typeIRightCreatedUnit q hq hq1 n hn l m c hadm t ∈
      physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        n l (m+1) 0 (c+1) (cupCreateRightIndex l m c t) := by
  change (typeIRightCreatedUnit q hq hq1 n hn l m c hadm t).val∈physicalTripleRightChannelGeneral
    q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+1) (c+1) _
  apply Submodule.smul_mem
  exact finiteTripleRightCreation_mem_successor q hq hq1 n hn l m c t _
    (physicalTypeIRightCoupling_mem_channel q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t)

theorem typeIRightCreatedUnit_norm_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    physicalTripleBilin q n l ((m+1)+0) (c+1)
      (typeIRightCreatedUnit q hq hq1 n hn l m c hadm t).val
      (typeIRightCreatedUnit q hq hq1 n hn l m c hadm t).val=1 := by
  unfold typeIRightCreatedUnit
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul,
    physicalTypeIHighestRightCreation_val,Nat.add_zero]
  change (typeIRightCreationScale q n l m c t)⁻¹ *
    ((typeIRightCreationScale q n l m c t)⁻¹ *
      physicalTripleBilin q n l (m+1) (c+1)
        (finiteTripleRightCreation q n l m c
          (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val)
        (finiteTripleRightCreation q n l m c
          (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val))=1
  have hm : (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val ∈
      physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        n l m c (physicalTypeIRightIndex l m 0 c t) :=
    physicalTypeIRightCoupling_mem_channel q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t
  have hg:=finiteTripleRightCreation_gram_channel q hq hq1 n hn l m c
    (physicalTypeIRightIndex l m 0 c t)
    (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val
    (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val hm hm
  have hu:=physicalTypeIRightCoupling_unit q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t
  simp only [Nat.add_zero] at hu
  rw [hg,hu,mul_one]
  have hs:=Real.sq_sqrt (mixedCreationSpectralScalar_pos q hq n m c (physicalTypeIRightIndex l m 0 c t).val).le
  have hnz:=ne_of_gt (typeIRightCreationScale_pos q hq n l m c t)
  change (typeIRightCreationScale q n l m c t)^2=_ at hs
  rw [← hs]
  field_simp

theorem typeIRightCreatedUnit_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    0 < typeIFirstBoundarySign n (m+1) (cupCreateRightIndex l m c t).val.val *
      physicalTypeIFirstBoundary n l (m+1) 0 (c+1)
        (typeIRightCreatedUnit q hq hq1 n hn l m c hadm t).val := by
  have ht:=t.val.isLt
  change 0 < typeIFirstBoundarySign n (m+1) t.val.val * _
  rw [typeIFirstBoundarySign_right_step n m t.val.val hn (by omega)]
  unfold typeIRightCreatedUnit
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul,physicalTypeIHighestRightCreation_val]
  rw [physicalTypeIFirstBoundary_right_creation]
  have hsq : (-1:ℝ)^n*(-1:ℝ)^n=1 := by rw [← mul_pow];norm_num
  have he : ((-1:ℝ)^n*typeIFirstBoundarySign n m t.val.val)*
      ((typeIRightCreationScale q n l m c t)⁻¹*
        (((-1:ℝ)^n*q^(-(n:ℤ)-(m:ℤ)-(c:ℤ)))*physicalTypeIFirstBoundary n l m 0 c
          (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val)) =
      ((-1:ℝ)^n*(-1:ℝ)^n)*((typeIRightCreationScale q n l m c t)⁻¹*
        q^(-(n:ℤ)-(m:ℤ)-(c:ℤ)))*
        (typeIFirstBoundarySign n m t.val.val*physicalTypeIFirstBoundary n l m 0 c
          (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val) := by ring
  rw [he,hsq,one_mul]
  exact mul_pos
    (mul_pos (inv_pos.mpr (typeIRightCreationScale_pos q hq n l m c t)) (zpow_pos hq _))
    (physicalTypeIRightCoupling_first_boundary_signed_pos q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t)

/-- Adding a reversed mixed contraction changes no Type-I right outer
vertex phase. The scalar is positive and belongs to that mixed vertex. -/
theorem physicalTypeIRightCoupling_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    finiteTripleRightCreation q n l m c
      (physicalTypeIRightCoupling q hq hq1 n hn l m 0 c hadm (Or.inl rfl) t).val =
      typeIRightCreationScale q n l m c t •
        (physicalTypeIRightCoupling q hq hq1 n hn l (m+1) 0 (c+1) (by omega) (Or.inl rfl)
          (cupCreateRightIndex l m c t)).val := by
  have hu:=physicalTypeIRightCoupling_unique_boundary q hq hq1 n hn l (m+1) 0 (c+1)
    (by omega) (Or.inl rfl) (cupCreateRightIndex l m c t)
    (typeIRightCreatedUnit q hq hq1 n hn l m c hadm t)
    (typeIRightCreatedUnit_mem q hq hq1 n hn l m c hadm t)
    (typeIRightCreatedUnit_norm_one q hq hq1 n hn l m c hadm t)
    (typeIRightCreatedUnit_boundary q hq hq1 n hn l m c hadm t)
  have hz:=ne_of_gt (typeIRightCreationScale_pos q hq n l m c t)
  calc
    _ = typeIRightCreationScale q n l m c t •
      (typeIRightCreatedUnit q hq hq1 n hn l m c hadm t).val := by
        unfold typeIRightCreatedUnit
        simp only [Submodule.coe_smul_of_tower,physicalTypeIHighestRightCreation_val,smul_smul,
          mul_inv_cancel₀ hz,one_smul]
    _ = _ := by rw [hu]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIRightCoupling_creation
