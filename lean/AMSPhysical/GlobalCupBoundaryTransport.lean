import GlobalCupFirstBoundary
import QuantumCupSpan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def cupFirstBoundaryEval (q : ℝ) (n l m h c : ℕ) : quantumCupSpan q n l m h c →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (cupFirstBoundaryPoint n l h c m 0)).comp
    (quantumCupSpan q n l m h c).subtype

theorem cupFirstBoundaryPoint_sum (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    cupFirstBoundaryPoint n l h c t k=cupFirstBoundaryPoint n l h c (t+k) 0 := by
  simp only [cupFirstBoundaryPoint,Nat.cast_add,Nat.cast_zero,add_zero]

theorem cupFirstBoundaryEval_vector (q : ℝ) (hq : q≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    cupFirstBoundaryEval q n l m h c (quantumCupVector q n l m h c r) =
      (-1:ℝ)^(n*(m-r.val.val))*
        q^((r.val.val:ℤ)*(1-(l:ℤ)-((m-r.val.val:ℕ):ℤ))+
          ((m-r.val.val:ℕ):ℤ)*(1-(n:ℤ)-(h:ℤ)-(c:ℤ))) := by
  have hr:=r.val.isLt
  have hs : r.val.val+(m-r.val.val)=m := by omega
  have hp:=cupFirstBoundaryPoint_sum n l h c r.val.val (m-r.val.val)
  rw [hs] at hp
  change quantumCupMonomial q n l h c r.val.val (m-r.val.val)
    (cupFirstBoundaryPoint n l h c m 0)=_
  rw [← hp]
  exact quantumCupMonomial_first_boundary q hq n hn l h c r.val.val (m-r.val.val)
    (by exact_mod_cast r.property.1) (by omega) (by exact_mod_cast r.property.2)

/-- On the same physical boundary, rank transport has one degree-dependent
sign, not a separately fitted sign for each cup term. -/
theorem quantumCupRankReduction_first_boundary (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    cupFirstBoundaryEval q 1 l m (h+n-1) c (quantumCupRankReduction q hq n hn l m h c v) =
      quantumCupRankGauge n m * cupFirstBoundaryEval q n l m h c v := by
  have he : (cupFirstBoundaryEval q 1 l m (h+n-1) c).comp
      (quantumCupRankReduction q hq n hn l m h c).toLinearMap =
      quantumCupRankGauge n m • cupFirstBoundaryEval q n l m h c := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumCupBasis_apply,
      quantumCupRankReduction_vector,map_smul,smul_eq_mul,LinearMap.smul_apply]
    rw [cupFirstBoundaryEval_vector q (ne_of_gt hq) 1 (by omega),
      cupFirstBoundaryEval_vector q (ne_of_gt hq) n hn]
    have hr:=r.val.isLt
    have hm : m=r.val.val+(m-r.val.val) := by omega
    have hcast : ((h+n-1:ℕ):ℤ)=(h:ℤ)+(n:ℤ)-1 := by omega
    have hexp : (r.val.val:ℤ)*(1-(l:ℤ)-((m-r.val.val:ℕ):ℤ))+
        ((m-r.val.val:ℕ):ℤ)*(1-(1:ℤ)-((h+n-1:ℕ):ℤ)-(c:ℤ)) =
        (r.val.val:ℤ)*(1-(l:ℤ)-((m-r.val.val:ℕ):ℤ))+
        ((m-r.val.val:ℕ):ℤ)*(1-(n:ℤ)-(h:ℤ)-(c:ℤ)) := by rw [hcast];ring
    simp only [Nat.cast_one,Nat.one_mul]
    rw [hexp]
    have hn' : n=(n-1)+1 := by omega
    have hsq : (-1:ℝ)^((n-1)*(m-r.val.val)) * (-1:ℝ)^((n-1)*(m-r.val.val))=1 := by
      rw [← mul_pow];norm_num
    have hsign : quantumCupRankGauge n r.val.val * (-1:ℝ)^(m-r.val.val) =
        quantumCupRankGauge n m * (-1:ℝ)^(n*(m-r.val.val)) := by
      unfold quantumCupRankGauge
      have hgm := congrArg (fun z : ℕ => (-1:ℝ)^((n-1)*z)) hm
      dsimp only at hgm
      rw [Nat.mul_add,pow_add] at hgm
      have hgn : (-1:ℝ)^(n*(m-r.val.val)) =
          (-1:ℝ)^((n-1)*(m-r.val.val)) * (-1:ℝ)^(m-r.val.val) := by
        calc
          _ = (-1:ℝ)^(((n-1)+1)*(m-r.val.val)) :=
            congrArg (fun z : ℕ => (-1:ℝ)^(z*(m-r.val.val))) hn'
          _ = _ := by rw [Nat.add_mul,Nat.one_mul,pow_add]
      rw [hgm,hgn]
      calc
        _ = ((-1:ℝ)^((n-1)*r.val.val)*(-1:ℝ)^(m-r.val.val))*1 := by ring
        _ = ((-1:ℝ)^((n-1)*r.val.val)*(-1:ℝ)^(m-r.val.val))*
          ((-1:ℝ)^((n-1)*(m-r.val.val))*(-1:ℝ)^((n-1)*(m-r.val.val))) :=
            congrArg (fun z : ℝ => ((-1:ℝ)^((n-1)*r.val.val)*(-1:ℝ)^(m-r.val.val))*z) hsq.symm
        _ = _ := by ring
    calc
      _ = (quantumCupRankGauge n r.val.val * (-1:ℝ)^(m-r.val.val))*
        q^((r.val.val:ℤ)*(1-(l:ℤ)-((m-r.val.val:ℕ):ℤ))+
          ((m-r.val.val:ℕ):ℤ)*(1-(n:ℤ)-(h:ℤ)-(c:ℤ))) := by ring
      _ = _ := by rw [hsign];ring
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.quantumCupRankReduction_first_boundary
