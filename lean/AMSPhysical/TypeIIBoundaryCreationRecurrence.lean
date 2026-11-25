import StandardBoundaryCreationCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The finite-range zero convention permits the linear quantum exponent
also at the endpoints, where the corresponding coefficient vanishes. -/
theorem standardBoundaryCoordinate_typeII_creation (q:ℝ) (hq:0<q) (h a b c k:ℕ)
    (w:finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)):
    standardBoundaryCoordinate (a+h) (b+h+1) (c+1) (k+h) k
      (typeIIStandardRightCreation q (a+h) (b+h) c w)=
      q^(-(b:ℤ)-(c:ℤ)+2*(k:ℤ))*standardBoundaryCoordinate (a+h) (b+h) c (k+h) k w-
        q^(-(h:ℤ)-1-(b:ℤ)-(c:ℤ))*
          (if k=0 then 0 else standardBoundaryCoordinate (a+h) (b+h) c ((k-1)+h) (k-1) w) := by
  rw [standardBoundaryCoordinate_creation]
  have he:q^(-1-((b+h:ℕ):ℤ)-(c:ℤ))=q^(-(h:ℤ)-1-(b:ℤ)-(c:ℤ)):=by
    congr 1
    push_cast
    ring
  rw [he]
  have hc:(if k=0 then 0 else standardBoundaryCoordinate (a+h) (b+h) c (k+h-1) (k-1) w)=
      (if k=0 then 0 else standardBoundaryCoordinate (a+h) (b+h) c ((k-1)+h) (k-1) w):=by
    by_cases hk:k=0
    · simp only [if_pos hk]
    · rw [if_neg hk,if_neg hk,show k+h-1=(k-1)+h from by omega]
  rw [hc]
  congr 1
  by_cases hk:k≤b ∧ k≤c
  · have hp: -((b+h-(k+h):ℕ):ℤ)-((c-k:ℕ):ℤ)= -(b:ℤ)-(c:ℤ)+2*(k:ℤ):=by omega
    rw [hp]
  · have hz:standardBoundaryCoordinate (a+h) (b+h) c (k+h) k=0:=by
      unfold standardBoundaryCoordinate
      split_ifs with hb hc
      · omega
      · rfl
      · rfl
    rw [hz,LinearMap.zero_apply,mul_zero,mul_zero]

end AMSPhysical
#print axioms AMSPhysical.standardBoundaryCoordinate_typeII_creation
