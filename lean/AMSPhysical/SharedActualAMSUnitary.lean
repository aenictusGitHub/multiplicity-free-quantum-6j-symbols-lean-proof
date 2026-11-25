import ActualUnitaryVertex

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Membership in the AMS set of actual trivalent triples. Construction
witnesses describe membership; they are not part of the table's index. -/
inductive ActualAMSVertex (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) :
    ActualIrrep q (h+1) → ActualIrrep q (h+1) → ActualIrrep q (h+1) → Prop where
  | forward (p s r : ℕ) : ActualAMSVertex q hq hq1 h
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
  | reverse (p s r : ℕ) : ActualAMSVertex q hq hq1 h
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
  | mixed_sym (p s c : ℕ) (hs : s≤c) : ActualAMSVertex q hq hq1 h
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s)).irrep
  | sym_mixed (a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) : ActualAMSVertex q hq hq1 h
      (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep
  | two_row (a b c d : ℕ) (r : TypeIICommonIndex a b c d) : ActualAMSVertex q hq hq1 h
      (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) b).irrep
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep
  | two_row_opp (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) : ActualAMSVertex q hq hq1 h
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep

theorem amsActualVertexTable_unitary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (A B C : ActualIrrep q (h+1)) (hRole : ActualAMSVertex q hq hq1 h A B C) :
    ActualUnitaryVertex (ne_of_gt hq) A B C (amsActualVertexTable q hq hq1 (h+1) (by omega) A B C) := by
  have H:=amsActualVertexTable_shared q hq hq1 h hh
  cases hRole with
  | forward p s r =>
    rw [H.forward p s r]
    apply canonicalizeActualVertex_unitary
    · exact globalMixedPairClebsch_intertwines q hq hq1 (h+1) (by omega) p s r
    · intro v w
      change LinearMap.BilinForm.tmul (occupationCompactBilin q (h+1) (p+r))
        (occupationOppositeBilin q (h+1) (s+r)) _ _=_
      rw [← mixedTensorBilin_eq_intrinsic]
      exact globalMixedPairClebsch_isometry q hq hq1 (h+1) (by omega) p s r v w
    · rw [← mul_pow];norm_num
  | reverse p s r =>
    rw [H.reverse p s r]
    apply canonicalizeActualVertex_unitary
    · exact globalReverseMixedPairClebsch_intertwines q hq hq1 (h+1) (by omega) p s r
    · intro v w
      change LinearMap.BilinForm.tmul (occupationOppositeBilin q (h+1) (s+r))
        (occupationCompactBilin q (h+1) (p+r)) _ _=_
      rw [← reverseMixedTensorBilin_eq_intrinsic]
      exact globalReverseMixedPairClebsch_isometry q hq hq1 (h+1) (by omega) p s r v w
    · norm_num
  | mixed_sym p s c hs =>
    rw [H.mixed_sym p s c hs]
    apply canonicalizeActualVertex_unitary
    · exact globalMixedSymVertex_intertwines q hq hq1 h p s c hs
    · exact globalMixedSymVertex_full_isometry q hq hq1 h p s c hs
    · norm_num
  | sym_mixed a p s d hbal hs =>
    rw [H.sym_mixed a p s d hbal hs]
    apply canonicalizeActualVertex_unitary
    · exact globalSymMixedVertex_intertwines q hq hq1 h a p s d hbal hs
    · exact globalSymMixedVertex_full_isometry q hq hq1 h a p s d hbal hs
    · rw [← mul_pow];norm_num
  | two_row a b c d r =>
    rw [H.two_row a b c d r]
    apply canonicalizeActualVertex_unitary
    · intro z v;rfl
    · intro v w
      change LinearMap.BilinForm.tmul (occupationCompactBilin q (h+1) a)
        (occupationCompactBilin q (h+1) b) v.val w.val=symmetricTensorBilin q (h+1) a b v.val w.val
      rw [← symmetricTensorBilin_eq_intrinsic]
    · norm_num
  | two_row_opp a b c d hbal r =>
    rw [H.two_row_opp a b c d hbal r]
    apply canonicalizeActualVertex_unitary
    · exact nativeTypeIIOuterVertex_intertwines q hq hq1 (h+1) (by omega) a b c d hbal r
    · exact nativeTypeIIOuterVertex_full_isometry q hq hq1 h a b c d hbal r
    · rw [← mul_pow];norm_num

theorem exists_shared_actual_unitary_AMS_vertex_table (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) :
    ∃ T : ActualVertexTable q (h+1),SharedActualAMSVertexTableSpec q hq hq1 h T ∧
      ∀ A B C,ActualAMSVertex q hq hq1 h A B C → ActualUnitaryVertex (ne_of_gt hq) A B C (T A B C) :=
  ⟨amsActualVertexTable q hq hq1 (h+1) (by omega),amsActualVertexTable_shared q hq hq1 h hh,
    amsActualVertexTable_unitary q hq hq1 h hh⟩

end AMSPhysical
#print axioms AMSPhysical.exists_shared_actual_unitary_AMS_vertex_table
