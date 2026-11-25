import ActualTwoRowOuterEntry
import ActualTwoRowDynkin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def ActualVertexTable (q : ℝ) (n : ℕ) := (A B C : ActualIrrep q n) →
  (fixedActualCarrier C).space →ₗ[ℝ] (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space

/-- One table on ordered actual Dynkin triples, with a single intrinsic
determinant-defect phase. Its indices contain no exterior or family tag. -/
def amsActualVertexTable (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n) : ActualVertexTable q n :=
  fun A B C => amsDynkinVertexPhase n A.val B.val C.val •
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn) A B C

theorem amsActualVertexTable_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (A B C : ActualIrrep q n)
    (F : (fixedActualCarrier C).space →ₗ[ℝ] (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space)
    (e : ℝ)
    (hF : actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn) A B C=F)
    (he : amsDynkinVertexPhase n A.val B.val C.val=e) :
    amsActualVertexTable q hq hq1 n hn A B C=e • F := by
  unfold amsActualVertexTable
  rw [hF,he]

/-- All six trivalent roles in the two AMS families use this same actual
table. Each equality is between full intertwining maps, not only coefficients. -/
structure SharedActualAMSVertexTableSpec (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (T : ActualVertexTable q (h+1)) : Prop where
  forward : ∀ p s r : ℕ,
    T (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep =
    (-1:ℝ)^(h*r) • canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
  reverse : ∀ p s r : ℕ,
    T (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep =
    (1:ℝ) • canonicalizeActualVertex (ne_of_gt hq)
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
  mixed_sym : ∀ (p s c : ℕ) (hs : s≤c),
    T (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s)).irrep =
    (1:ℝ) • canonicalizeActualVertex (ne_of_gt hq)
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (actualSymmetricCarrier q hq hq1 (h+1) c)
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s)) (globalMixedSymVertex q hq hq1 h p s c hs)
  sym_mixed : ∀ (a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a),
    T (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep =
    (-1:ℝ)^(h*s) • canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) a)
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (actualSymmetricCarrier q hq hq1 (h+1) d) (globalSymMixedVertex q hq hq1 h a p s d hbal hs)
  two_row : ∀ (a b c d : ℕ) (r : TypeIICommonIndex a b c d),
    T (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) b).irrep
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep =
    (1:ℝ) • canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) b)
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r)
      (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channel.subtype
  two_row_opp : ∀ (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d),
    T (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep =
    (-1:ℝ)^(h*c) • canonicalizeActualVertex (ne_of_gt hq)
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r)
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c)
      (actualSymmetricCarrier q hq hq1 (h+1) d)
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r)

theorem amsActualVertexTable_shared (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h) :
    SharedActualAMSVertexTableSpec q hq hq1 h (amsActualVertexTable q hq hq1 (h+1) (by omega)) := by
  constructor
  · intro p s r
    apply amsActualVertexTable_entry
    · exact actualPositiveVertexTable_forward_entry q hq hq1 (h+1) (by omega) p s r
    · change amsDynkinVertexPhase (h+1) (mixedHighestDynkin (h+1) (p+r) 0)
        (mixedHighestDynkin (h+1) 0 (s+r)) (mixedHighestDynkin (h+1) p s)=_
      simpa only [Nat.add_sub_cancel] using amsDynkinVertexPhase_forward (h+1) (by omega) p s r
  · intro p s r
    apply amsActualVertexTable_entry
    · exact actualPositiveVertexTable_reverse_entry q hq hq1 (h+1) (by omega) p s r
    · exact amsDynkinVertexPhase_reverse (h+1) p s r
  · intro p s c hs
    apply amsActualVertexTable_entry
    · exact actualPositiveVertexTable_mixed_sym_entry q hq hq1 h hh p s c hs
    · exact amsDynkinVertexPhase_mixed_sym (h+1) p s c (p+c-s)
  · intro a p s d hbal hs
    apply amsActualVertexTable_entry
    · exact actualPositiveVertexTable_sym_mixed_entry q hq hq1 h hh a p s d hbal hs
    · change amsDynkinVertexPhase (h+1) (mixedHighestDynkin (h+1) a 0)
        (mixedHighestDynkin (h+1) p s) (mixedHighestDynkin (h+1) d 0)=_
      simpa only [Nat.add_sub_cancel] using amsDynkinVertexPhase_sym_mixed (h+1) (by omega) a p s d hbal
  · intro a b c d r
    apply amsActualVertexTable_entry
    · exact actualPositiveVertexTable_native_twoRow_entry q hq hq1 (h+1) (by omega) a b c d r
    · exact amsDynkinVertexPhase_symmetric_second (h+1) b _ _
  · intro a b c d hbal r
    apply amsActualVertexTable_entry
    · exact actualPositiveVertexTable_twoRow_outer_entry q hq hq1 h hh a b c d hbal r
    · change amsDynkinVertexPhase (h+1) (twoRowHighestWeight (h+1) (by omega) (a+b) 0 r.val)
        (mixedHighestDynkin (h+1) 0 c) (mixedHighestDynkin (h+1) d 0)=_
      simpa only [Nat.add_sub_cancel] using amsDynkinVertexPhase_twoRow_outer (h+1) (by omega)
        (a+b) r.val c d (by have hr:=r.isLt;omega) hbal.symm

/-- Existence of one shared actual AMS vertex table for both families at
every N=h+2 >=3, including all coincident native irrep descriptions. -/
theorem exists_shared_actual_AMS_vertex_table (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h) :
    ∃ T : ActualVertexTable q (h+1),SharedActualAMSVertexTableSpec q hq hq1 h T :=
  ⟨amsActualVertexTable q hq hq1 (h+1) (by omega),amsActualVertexTable_shared q hq hq1 h hh⟩

end AMSPhysical
#print axioms AMSPhysical.exists_shared_actual_AMS_vertex_table
