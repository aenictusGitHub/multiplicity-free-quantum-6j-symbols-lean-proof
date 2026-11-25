import QuantumCupSpan
import QuantumCupIndexSteps

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupLeftRadial_vector (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomialAt q n l m h c r))=
      quantumCupLeftDiagonal q n (l:ℤ) (h:ℤ) r.val.val (m-r.val.val) • quantumCupMonomialAt q n l m h c r+
        if hr : quantumCupCanRaiseLeft l m c r then
          quantumCupLeftOffDiagonal q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val) •
            quantumCupMonomialAt q n l m h c (quantumCupRaiseLeft l m c r hr) else 0 := by
  change tripleLeftCreation q n (tripleLeftAnnihilation q n
    (quantumCupMonomial q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val)))=_
  rw [quantumCupLeftRadial_all q hq hD n hn]
  by_cases hs : quantumCupCanRaiseLeft l m c r
  · rw [dif_pos hs]
    unfold quantumCupMonomialAt
    rw [quantumCupRaiseLeft_rightCount]
    rfl
  · rw [dif_neg hs,quantumCupLeftOffDiagonal_boundary_zero q n l m c (h:ℤ) r hs,zero_smul]
    rfl

theorem quantumCupRightRadial_vector (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomialAt q n l m h c r))=
      quantumCupLeftDiagonal q n (c:ℤ) (h:ℤ) (m-r.val.val) r.val.val • quantumCupMonomialAt q n l m h c r+
        if hr : quantumCupCanRaiseRight l m c r then
          quantumCupLeftOffDiagonal q n (c:ℤ) (h:ℤ) (l:ℤ) (m-r.val.val) r.val.val •
            quantumCupMonomialAt q n l m h c (quantumCupRaiseRight l m c r hr) else 0 := by
  change tripleRightCreation q n (tripleRightAnnihilation q n
    (quantumCupMonomial q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val)))=_
  rw [quantumCupRightRadial_all q hq hD n hn]
  by_cases hs : quantumCupCanRaiseRight l m c r
  · rw [dif_pos hs]
    unfold quantumCupMonomialAt
    rw [quantumCupRaiseRight_rightCount]
    rfl
  · rw [dif_neg hs,quantumCupRightOffDiagonal_boundary_zero q n l m c (h:ℤ) r hs,zero_smul]
    rfl

theorem quantumCupLeftRadial_mem (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomialAt q n l m h c r))∈quantumCupSpan q n l m h c := by
  rw [quantumCupLeftRadial_vector q hq hD n hn]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (quantumCupVector q n l m h c r).property
  · split_ifs with hs
    · exact Submodule.smul_mem _ _ (quantumCupVector q n l m h c (quantumCupRaiseLeft l m c r hs)).property
    · exact Submodule.zero_mem _

theorem quantumCupRightRadial_mem (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomialAt q n l m h c r))∈quantumCupSpan q n l m h c := by
  rw [quantumCupRightRadial_vector q hq hD n hn]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (quantumCupVector q n l m h c r).property
  · split_ifs with hs
    · exact Submodule.smul_mem _ _ (quantumCupVector q n l m h c (quantumCupRaiseRight l m c r hs)).property
    · exact Submodule.zero_mem _

theorem quantumCupLeftRadial_preserves (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : OccupationTripleLattice n →₀ ℝ) (hv : v∈quantumCupSpan q n l m h c) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n v)∈quantumCupSpan q n l m h c := by
  induction hv using Submodule.span_induction with
  | mem w hw => obtain ⟨r,rfl⟩:=hw;exact quantumCupLeftRadial_mem q hq hD n hn l m h c r
  | zero => simp only [map_zero];exact Submodule.zero_mem _
  | add x y hx hy hix hiy => simp only [map_add];exact Submodule.add_mem _ hix hiy
  | smul a x hx hix => simp only [map_smul];exact Submodule.smul_mem _ _ hix

theorem quantumCupRightRadial_preserves (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : OccupationTripleLattice n →₀ ℝ) (hv : v∈quantumCupSpan q n l m h c) :
    tripleRightCreation q n (tripleRightAnnihilation q n v)∈quantumCupSpan q n l m h c := by
  induction hv using Submodule.span_induction with
  | mem w hw => obtain ⟨r,rfl⟩:=hw;exact quantumCupRightRadial_mem q hq hD n hn l m h c r
  | zero => simp only [map_zero];exact Submodule.zero_mem _
  | add x y hx hy hix hiy => simp only [map_add];exact Submodule.add_mem _ hix hiy
  | smul a x hx hix => simp only [map_smul];exact Submodule.smul_mem _ _ hix

end AMSPhysical
