import QuantumCupBoundaryDiagonal
import TriangularFamilyIndependent

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def QuantumCupIndex (l m c : ℕ) := {t : Fin (m+1) // t.val ≤ l ∧ m-t.val ≤ c}

instance quantumCupIndexFintype (l m c : ℕ) : Fintype (QuantumCupIndex l m c) := inferInstanceAs
  (Fintype {t : Fin (m+1) // t.val ≤ l ∧ m-t.val ≤ c})

instance quantumCupIndexDecidableEq (l m c : ℕ) : DecidableEq (QuantumCupIndex l m c) :=
  inferInstanceAs (DecidableEq {t : Fin (m+1) // t.val ≤ l ∧ m-t.val ≤ c})

def quantumCupMonomialAt (q : ℝ) (n l m h c : ℕ) (r : QuantumCupIndex l m c) : OccupationTripleLattice n →₀ ℝ :=
  quantumCupMonomial q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val)

theorem quantumCupMonomialAt_linearIndependent (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) : LinearIndependent ℝ (quantumCupMonomialAt q n l m h c) := by
  apply triangularFamily_linearIndependent (quantumCupMonomialAt q n l m h c)
    (fun r : QuantumCupIndex l m c =>r.val.val)
    (by intro r s hs;apply Subtype.ext;exact Fin.ext hs)
    (fun y =>Finsupp.lapply (quantumCupBoundaryPoint n (l:ℤ) (h:ℤ) (c:ℤ) y (m-y)))
  · intro r y hy
    change quantumCupMonomial q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val)
      (quantumCupBoundaryPoint n (l:ℤ) (h:ℤ) (c:ℤ) y (m-y))=0
    apply quantumCupBoundary_above_zero q n hn
    have hr:=r.val.isLt
    omega
  · intro r
    change quantumCupMonomial q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val)
      (quantumCupBoundaryPoint n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val))≠0
    exact ne_of_gt (quantumCupBoundary_diagonal_pos q hq n hn (l:ℤ) (h:ℤ) (c:ℤ)
      r.val.val (m-r.val.val) (by exact_mod_cast r.property.1) (by omega) (by exact_mod_cast r.property.2))

end AMSPhysical
#print axioms AMSPhysical.quantumCupMonomialAt_linearIndependent
