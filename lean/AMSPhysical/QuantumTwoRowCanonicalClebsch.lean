import QuantumTwoRowNormalized

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
attribute [local irreducible] typeASymmetricTensor symmetricTensorBilin normalizedTwoRowHighest
open scoped TensorProduct

def twoRowCanonicalTransport (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m') :
    normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r hl hm ≃ₗ[ℝ]
      normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l' m' r hl' hm' := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) l' ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m'
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact CompactHighestRealization.transport (V:=V) (W:=W) (ne_of_gt hq)
    (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
    (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm')

theorem twoRowCanonicalTransport_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m')
    (x y : normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r hl hm) :
    symmetricTensorBilin q n l m x.val y.val=
      symmetricTensorBilin q n l' m' (twoRowCanonicalTransport q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' x).val
        (twoRowCanonicalTransport q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' y).val := by
  exact CompactHighestRealization.transport_isometry (ne_of_gt hq)
    (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
    (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm') x y

theorem twoRowCanonicalTransport_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m') (z : UqTypeA q n)
    (x : normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r hl hm) :
    (twoRowCanonicalTransport q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm'
      ⟨typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z x.val,
        algebraCyclicSpan_invariant _ _ z x.val x.property⟩).val=
      typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l' m' z
        (twoRowCanonicalTransport q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' x).val := by
  exact CompactHighestRealization.transport_intertwines (ne_of_gt hq)
    (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
    (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm') z x

/-- One fixed physical carrier for each two-row highest weight. -/
abbrev canonicalTwoRowModel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (a b : ℕ) :=
  normalizedTwoRowChannel q hq hD n hn (a+b) b b (by omega) (le_refl b)

def canonicalTwoRowClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b l m : ℕ) (hS : l+m=a+2*b) (hl : b≤l) (hm : b≤m) :
    canonicalTwoRowModel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn a b →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  (normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m b hl hm).subtype.comp
    (twoRowCanonicalTransport q hq hq1 n hn (a+2*b) b (a+b) b l m (by omega) hS (by omega) (le_refl b) hl hm).toLinearMap

theorem canonicalTwoRowClebsch_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b l m : ℕ) (hS : l+m=a+2*b) (hl : b≤l) (hm : b≤m)
    (x y : canonicalTwoRowModel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn a b) :
    symmetricTensorBilin q n l m (canonicalTwoRowClebsch q hq hq1 n hn a b l m hS hl hm x)
      (canonicalTwoRowClebsch q hq hq1 n hn a b l m hS hl hm y)=symmetricTensorBilin q n (a+b) b x.val y.val := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) (a+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  let W := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  simp only [canonicalTwoRowClebsch,LinearMap.comp_apply,Submodule.subtype_apply,LinearEquiv.coe_coe]
  exact (twoRowCanonicalTransport_isometry q hq hq1 n hn (a+2*b) b (a+b) b l m (by omega) hS (by omega) (le_refl b) hl hm x y).symm

theorem canonicalTwoRowClebsch_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b l m : ℕ) (hS : l+m=a+2*b) (hl : b≤l) (hm : b≤m) (z : UqTypeA q n)
    (x : canonicalTwoRowModel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn a b) :
    canonicalTwoRowClebsch q hq hq1 n hn a b l m hS hl hm
      ⟨typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (a+b) b z x.val,
        algebraCyclicSpan_invariant _ _ z x.val x.property⟩=
      typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
        (canonicalTwoRowClebsch q hq hq1 n hn a b l m hS hl hm x) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) (a+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  let W := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  simp only [canonicalTwoRowClebsch,LinearMap.comp_apply,Submodule.subtype_apply,LinearEquiv.coe_coe]
  exact twoRowCanonicalTransport_intertwines q hq hq1 n hn (a+2*b) b (a+b) b l m (by omega) hS (by omega) (le_refl b) hl hm z x

end AMSPhysical
#print axioms AMSPhysical.canonicalTwoRowClebsch_intertwines
