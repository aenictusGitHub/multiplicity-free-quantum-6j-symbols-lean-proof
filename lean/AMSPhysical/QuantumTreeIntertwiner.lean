import QuantumRecouplingConstruction
import QuantumTripleRepresentation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem quantumLeftTreeMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s : Fin (min (coupledLabel l m r) n+1)) :
    IsQuantumIntertwiner
      (V:=RealQuantumSpace (coupledLabel (coupledLabel l m r) n s)) (W:=RealQuantumTripleSpace l m n) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (coupledLabel (coupledLabel l m r) n s))
      (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
      (quantumLeftTreeMap q hq hq1 l m n r s) := by
  let hd := qInteger_denominator_ne_zero q hq hq1
  let ρi := finiteQuantumRepresentation q (ne_of_gt hq) hd (coupledLabel l m r)
  let ρn := finiteQuantumRepresentation q (ne_of_gt hq) hd n
  let ρlm := finiteTensorRepresentation q (ne_of_gt hq) hd l m
  have ht := quantumIntertwiner_tensor
    (V:=RealQuantumSpace (coupledLabel l m r)) (W:=RealQuantumSpace n)
    (V':=RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) (W':=RealQuantumSpace n)
    q (ne_of_gt hq) ρi ρn ρlm ρn (unitaryQuantumClebschMap q hq hq1 l m r) 1
    (unitaryQuantumClebschMap_intertwines q hq hq1 l m r) (fun _ _ => rfl)
  exact quantumIntertwiner_comp
    (V:=RealQuantumSpace (coupledLabel (coupledLabel l m r) n s))
    (W:=RealQuantumSpace (coupledLabel l m r) ⊗[ℝ] RealQuantumSpace n) (U:=RealQuantumTripleSpace l m n)
    q (finiteQuantumRepresentation q (ne_of_gt hq) hd (coupledLabel (coupledLabel l m r) n s))
    (finiteTensorRepresentation q (ne_of_gt hq) hd (coupledLabel l m r) n)
    (finiteTripleRepresentation q (ne_of_gt hq) hd l m n)
    (unitaryQuantumClebschMap q hq hq1 (coupledLabel l m r) n s)
    (TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m r) 1)
    (unitaryQuantumClebschMap_intertwines q hq hq1 (coupledLabel l m r) n s) ht

theorem quantumRightTreeMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1)) :
    IsQuantumIntertwiner
      (V:=RealQuantumSpace (coupledLabel l (coupledLabel m n u) v)) (W:=RealQuantumTripleSpace l m n) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (coupledLabel l (coupledLabel m n u) v))
      (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
      (quantumRightTreeMap q hq hq1 l m n u v) := by
  let hd := qInteger_denominator_ne_zero q hq hq1
  have ht : IsQuantumIntertwiner
      (V:=RealQuantumSpace l ⊗[ℝ] RealQuantumSpace (coupledLabel m n u))
      (W:=RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)) q
      (finiteTensorRepresentation q (ne_of_gt hq) hd l (coupledLabel m n u))
      (finiteRightTripleRepresentation q (ne_of_gt hq) hd l m n)
      (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u)) := by
    exact quantumIntertwiner_tensor
      (V:=RealQuantumSpace l) (W:=RealQuantumSpace (coupledLabel m n u))
      (V':=RealQuantumSpace l) (W':=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
      q (ne_of_gt hq)
      (finiteQuantumRepresentation q (ne_of_gt hq) hd l)
      (finiteQuantumRepresentation q (ne_of_gt hq) hd (coupledLabel m n u))
      (finiteQuantumRepresentation q (ne_of_gt hq) hd l)
      (finiteTensorRepresentation q (ne_of_gt hq) hd m n)
      1 (unitaryQuantumClebschMap q hq hq1 m n u)
      (fun _ _ => rfl) (unitaryQuantumClebschMap_intertwines q hq hq1 m n u)
  have ha := quantumIntertwiner_inverse
    (V:=RealQuantumTripleSpace l m n)
    (W:=RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)) q
    (finiteTripleRepresentation q (ne_of_gt hq) hd l m n)
    (finiteRightTripleRepresentation q (ne_of_gt hq) hd l m n)
    (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n))
    (finiteTripleRepresentation_assoc q (ne_of_gt hq) hd l m n)
  have ha' (x : UqSL2 q)
      (w : RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)) :
      finiteTripleRepresentation q (ne_of_gt hq) hd l m n x
        ((TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).symm w)=
      (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).symm
        (finiteRightTripleRepresentation q (ne_of_gt hq) hd l m n x w) := ha x w
  intro x p
  change finiteTripleRepresentation q (ne_of_gt hq) hd l m n x
      ((TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).symm
        (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u)
          (unitaryQuantumClebschMap q hq hq1 l (coupledLabel m n u) v p)))=
    (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).symm
      (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u)
        (unitaryQuantumClebschMap q hq hq1 l (coupledLabel m n u) v
          (finiteQuantumRepresentation q (ne_of_gt hq) hd (coupledLabel l (coupledLabel m n u) v) x p)))
  rw [ha' x _,ht x _,unitaryQuantumClebschMap_intertwines q hq hq1 l (coupledLabel m n u) v x p]

end AMSPhysical

#print axioms AMSPhysical.quantumLeftTreeMap_intertwines
#print axioms AMSPhysical.quantumRightTreeMap_intertwines
