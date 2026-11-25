import RankTwoHighestEquivalence
import QuantumCupFusionPaths
import QuantumFusionHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem mixedHighestDynkin_symmetric_rankTwo (H : ℕ) (i : Fin 1) :
    mixedHighestDynkin 1 H 0 i=(H:ℤ) := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  have hc : (0:Fin 1).castSucc=(0:Fin 2) := by decide
  simp only [mixedHighestDynkin,if_pos hc,mul_one,Nat.cast_zero,zero_mul,add_zero]

theorem standardTypeAHighest_mem_iff (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m c H : ℕ)
    (v : RealQuantumTripleSpace l m c) :
    v∈standardTypeAHighestMultiplicity q hq hD l m c H ↔
      finiteTripleRepresentation q hq hD l m c (uqGenerator q 0) v=0 ∧
        finiteTripleRepresentation q hq hD l m c (uqGenerator q 2) v=q^(H:ℤ) • v := by
  rw [mem_typeAHighestSpace]
  simp only [AlgHom.comp_apply,rankTwoToSL2_generator,mixedHighestDynkin_symmetric_rankTwo]
  constructor
  · rintro ⟨hE,hK⟩;exact ⟨hE 0,hK 0⟩
  · rintro ⟨hE,hK⟩;exact ⟨fun _ =>hE,fun _ =>hK⟩

def standardCupLeftHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (t : QuantumCupIndex l m c) :
    standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l (m+b) c (l+c-m+b) := by
  let p:=quantumCupLeftPath l m b c t
  refine ⟨quantumLeftTreeHighest q hq hq1 l (m+b) c p.1 p.2,?_⟩
  apply (standardTypeAHighest_mem_iff q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l (m+b) c (l+c-m+b) _).mpr
  refine ⟨quantumLeftTreeHighest_E q hq hq1 l (m+b) c p,?_⟩
  have he:=quantumLeftTreeHighest_K q hq hq1 l (m+b) c p
  change _=q^(leftTotalLabel l (m+b) c p:ℤ) • _ at he
  rw [quantumCupLeftPath_total l m b c hadm t] at he
  exact he

def standardCupRightHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (t : QuantumCupIndex l m c) :
    standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l (m+b) c (l+c-m+b) := by
  let p:=quantumCupRightPath l m b c t
  refine ⟨quantumRightTreeHighest q hq hq1 l (m+b) c p.1 p.2,?_⟩
  apply (standardTypeAHighest_mem_iff q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l (m+b) c (l+c-m+b) _).mpr
  refine ⟨quantumRightTreeHighest_E q hq hq1 l (m+b) c p,?_⟩
  have he:=quantumRightTreeHighest_K q hq hq1 l (m+b) c p
  change _=q^(rightTotalLabel l (m+b) c p:ℤ) • _ at he
  rw [quantumCupRightPath_total l m b c hadm t] at he
  exact he

theorem standardCupLeftHighest_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (t : QuantumCupIndex l m c) :
    quantumTripleBilin q l (m+b) c (standardCupLeftHighest q hq hq1 l m b c hadm t).val
      (standardCupLeftHighest q hq hq1 l m b c hadm t).val=1 :=
  quantumLeftTreeHighest_unit q hq hq1 l (m+b) c (quantumCupLeftPath l m b c t).1 (quantumCupLeftPath l m b c t).2

theorem standardCupRightHighest_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (t : QuantumCupIndex l m c) :
    quantumTripleBilin q l (m+b) c (standardCupRightHighest q hq hq1 l m b c hadm t).val
      (standardCupRightHighest q hq hq1 l m b c hadm t).val=1 :=
  quantumRightTreeHighest_unit q hq hq1 l (m+b) c (quantumCupRightPath l m b c t).1 (quantumCupRightPath l m b c t).2

theorem standardCupHighest_overlap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (s t : QuantumCupIndex l m c) :
    quantumTripleBilin q l (m+b) c (standardCupLeftHighest q hq hq1 l m b c hadm s).val
      (standardCupRightHighest q hq hq1 l m b c hadm t).val=
      quantumRacahMatrix q hq hq1 l (m+b) c (quantumCupLeftPath l m b c s) (quantumCupRightPath l m b c t) := rfl

end AMSPhysical
#print axioms AMSPhysical.standardCupHighest_overlap
