import QuantumCupSpan
import QuantumCupReverseMonomial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical

def cupCreateLeftIndex (l m c : ℕ) (r : QuantumCupIndex l m c) :
    QuantumCupIndex (l+1) (m+1) c :=
  ⟨⟨r.val.val+1, by have hr:=r.val.isLt;omega⟩,
    by change r.val.val+1≤l+1 ∧ m+1-(r.val.val+1)≤c
       have hl:=r.property.1;have hc:=r.property.2;omega⟩

def cupCreateRightIndex (l m c : ℕ) (r : QuantumCupIndex l m c) :
    QuantumCupIndex l (m+1) (c+1) :=
  ⟨⟨r.val.val, by have hr:=r.val.isLt;omega⟩,
    by change r.val.val≤l ∧ m+1-r.val.val≤c+1
       have hl:=r.property.1;have hc:=r.property.2;omega⟩

theorem quantumCupMonomialAt_create_left (q : ℝ) (n l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    tripleLeftCreation q n (quantumCupMonomialAt q n l m h c r) =
      quantumCupMonomialAt q n (l+1) (m+1) h c (cupCreateLeftIndex l m c r) := by
  unfold quantumCupMonomialAt cupCreateLeftIndex quantumCupMonomial
  simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
  rw [show (l:ℤ)+1-((r.val.val:ℤ)+1)=(l:ℤ)-(r.val.val:ℤ) by ring,
    pow_succ', Module.End.mul_apply]

theorem quantumCupMonomialAt_create_right (q : ℝ) (hq : q≠0) (n l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    tripleRightCreation q n (quantumCupMonomialAt q n l m h c r) =
      quantumCupMonomialAt q n l (m+1) h (c+1) (cupCreateRightIndex l m c r) := by
  have hr:=r.val.isLt
  have he : m+1-r.val.val=(m-r.val.val)+1 := by omega
  unfold quantumCupMonomialAt cupCreateRightIndex
  rw [he, quantumCupMonomial_reverse q hq, quantumCupMonomial_reverse q hq]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (c:ℤ)+1-(((m-r.val.val:ℕ):ℤ)+1)=(c:ℤ)-((m-r.val.val:ℕ):ℤ) by ring,
    pow_succ', Module.End.mul_apply]

/-- The literal left cup creation, restricted to independently constructed
cup spans in neighboring exterior degrees. -/
def cupLeftCreation (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    quantumCupSpan q n l m h c →ₗ[ℝ] quantumCupSpan q n (l+1) (m+1) h c :=
  (quantumCupBasis q hq n hn l m h c).constr ℝ
    (fun r => quantumCupVector q n (l+1) (m+1) h c (cupCreateLeftIndex l m c r))

def cupRightCreation (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    quantumCupSpan q n l m h c →ₗ[ℝ] quantumCupSpan q n l (m+1) h (c+1) :=
  (quantumCupBasis q hq n hn l m h c).constr ℝ
    (fun r => quantumCupVector q n l (m+1) h (c+1) (cupCreateRightIndex l m c r))

theorem cupLeftCreation_vector (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    cupLeftCreation q hq n hn l m h c (quantumCupVector q n l m h c r) =
      quantumCupVector q n (l+1) (m+1) h c (cupCreateLeftIndex l m c r) := by
  rw [← quantumCupBasis_apply q hq n hn l m h c r]
  exact Module.Basis.constr_basis _ _ _ _

theorem cupRightCreation_vector (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (r : QuantumCupIndex l m c) :
    cupRightCreation q hq n hn l m h c (quantumCupVector q n l m h c r) =
      quantumCupVector q n l (m+1) h (c+1) (cupCreateRightIndex l m c r) := by
  rw [← quantumCupBasis_apply q hq n hn l m h c r]
  exact Module.Basis.constr_basis _ _ _ _

theorem cupLeftCreation_literal (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (v : quantumCupSpan q n l m h c) :
    (cupLeftCreation q hq n hn l m h c v).val=tripleLeftCreation q n v.val := by
  have he : (quantumCupSpan q n (l+1) (m+1) h c).subtype.comp
      (cupLeftCreation q hq n hn l m h c) =
      (tripleLeftCreation q n).comp (quantumCupSpan q n l m h c).subtype := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, quantumCupBasis_apply, cupLeftCreation_vector,
      Submodule.subtype_apply]
    exact (quantumCupMonomialAt_create_left q n l m h c r).symm
  exact DFunLike.congr_fun he v

theorem cupRightCreation_literal (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (v : quantumCupSpan q n l m h c) :
    (cupRightCreation q hq n hn l m h c v).val=tripleRightCreation q n v.val := by
  have he : (quantumCupSpan q n l (m+1) h (c+1)).subtype.comp
      (cupRightCreation q hq n hn l m h c) =
      (tripleRightCreation q n).comp (quantumCupSpan q n l m h c).subtype := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, quantumCupBasis_apply, cupRightCreation_vector,
      Submodule.subtype_apply]
    exact (quantumCupMonomialAt_create_right q (ne_of_gt hq) n l m h c r).symm
  exact DFunLike.congr_fun he v

/-- The only sign in transport through a left degree step is (-1)^(N-2),
independent of the exterior quadruple and of the cup channel. -/
theorem quantumCupRankReduction_create_left (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    quantumCupRankReduction q hq n hn (l+1) (m+1) h c
      (cupLeftCreation q hq n hn l m h c v) =
      (-1:ℝ)^(n-1) • cupLeftCreation q hq 1 (by omega) l m (h+n-1) c
        (quantumCupRankReduction q hq n hn l m h c v) := by
  have he : (quantumCupRankReduction q hq n hn (l+1) (m+1) h c).toLinearMap.comp
      (cupLeftCreation q hq n hn l m h c) =
      (-1:ℝ)^(n-1) • (cupLeftCreation q hq 1 (by omega) l m (h+n-1) c).comp
        (quantumCupRankReduction q hq n hn l m h c).toLinearMap := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, quantumCupBasis_apply, cupLeftCreation_vector,
      quantumCupRankReduction_vector, map_smul, LinearMap.smul_apply, smul_smul]
    change quantumCupRankGauge n (r.val.val+1) • _ =
      ((-1:ℝ)^(n-1)*quantumCupRankGauge n r.val.val) • _
    rw [quantumCupRankGauge_succ, mul_comm]
  exact DFunLike.congr_fun he v

theorem quantumCupRankReduction_create_right (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    quantumCupRankReduction q hq n hn l (m+1) h (c+1)
      (cupRightCreation q hq n hn l m h c v) =
      cupRightCreation q hq 1 (by omega) l m (h+n-1) c
        (quantumCupRankReduction q hq n hn l m h c v) := by
  have he : (quantumCupRankReduction q hq n hn l (m+1) h (c+1)).toLinearMap.comp
      (cupRightCreation q hq n hn l m h c) =
      (cupRightCreation q hq 1 (by omega) l m (h+n-1) c).comp
        (quantumCupRankReduction q hq n hn l m h c).toLinearMap := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, quantumCupBasis_apply, cupRightCreation_vector,
      quantumCupRankReduction_vector, map_smul]
    rfl
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.quantumCupRankReduction_create_left
#print axioms AMSPhysical.quantumCupRankReduction_create_right
