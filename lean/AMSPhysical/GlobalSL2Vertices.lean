import QuantumRecouplingConstruction
import QuantumBoundaryRecoupling
import GlobalVertexSigns

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- A single actual unitary CG embedding for each admissible ordered sl2
fusion triple; r is uniquely determined by the three incident labels. -/
def globalSL2Vertex (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b : ℕ)
    (r : Fin (min a b + 1)) :
    RealQuantumSpace (coupledLabel a b r) →ₗ[ℝ]
      RealQuantumSpace a ⊗[ℝ] RealQuantumSpace b :=
  unitaryQuantumClebschMap q hq hq1 a b r

theorem globalSL2Vertex_output_unique (a b : ℕ) (r s : Fin (min a b + 1))
    (h : coupledLabel a b r = coupledLabel a b s) : r = s := by
  have hr := r.isLt
  have hs := s.isLt
  apply Fin.ext
  unfold coupledLabel at h
  omega

theorem globalSL2Vertex_isometry (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b : ℕ)
    (r : Fin (min a b + 1)) (x y : RealQuantumSpace (coupledLabel a b r)) :
    quantumTensorBilin q a b (globalSL2Vertex q hq hq1 a b r x)
      (globalSL2Vertex q hq hq1 a b r y) = quantumPair q (coupledLabel a b r) x y :=
  unitaryQuantumClebschMap_isometry q hq hq1 a b r x y

def globalSL2LeftTree (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b c : ℕ)
    (r : Fin (min a b + 1)) (s : Fin (min (coupledLabel a b r) c + 1)) :=
  (TensorProduct.map (globalSL2Vertex q hq hq1 a b r) (LinearMap.id : Module.End ℝ (RealQuantumSpace c))).comp
    (globalSL2Vertex q hq hq1 (coupledLabel a b r) c s)

def globalSL2RightTree (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b c : ℕ)
    (r : Fin (min b c + 1)) (s : Fin (min a (coupledLabel b c r) + 1)) :=
  (TensorProduct.assoc ℝ (RealQuantumSpace a) (RealQuantumSpace b) (RealQuantumSpace c)).symm.toLinearMap.comp
    ((TensorProduct.map (LinearMap.id : Module.End ℝ (RealQuantumSpace a))
      (globalSL2Vertex q hq hq1 b c r)).comp
        (globalSL2Vertex q hq hq1 a (coupledLabel b c r) s))

theorem globalSL2LeftTree_eq (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b c : ℕ)
    (r : Fin (min a b + 1)) (s : Fin (min (coupledLabel a b r) c + 1)) :
    globalSL2LeftTree q hq hq1 a b c r s = quantumLeftTreeMap q hq hq1 a b c r s := rfl

theorem globalSL2RightTree_eq (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b c : ℕ)
    (r : Fin (min b c + 1)) (s : Fin (min a (coupledLabel b c r) + 1)) :
    globalSL2RightTree q hq hq1 a b c r s = quantumRightTreeMap q hq hq1 a b c r s := rfl

/-- The global family is reused in every left/right tree, for all exterior
labels. This entry is an overlap of those actual trees, not a factorial sum. -/
def globalSL2Recoupling (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b c : ℕ)
    (p : LeftHighestPath a b c) (t : RightHighestPath a b c) : ℝ :=
  quantumTripleBilin q a b c
    (globalSL2LeftTree q hq hq1 a b c p.1 p.2 (standardWeightBasis _ 0))
    (globalSL2RightTree q hq hq1 a b c t.1 t.2 (standardWeightBasis _ 0))

theorem globalSL2Recoupling_eq (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) (a b c : ℕ)
    (p : LeftHighestPath a b c) (t : RightHighestPath a b c) :
    globalSL2Recoupling q hq hq1 a b c p t = quantumRacahMatrix q hq hq1 a b c p t := rfl

end AMSPhysical
#print axioms AMSPhysical.globalSL2Vertex_isometry
#print axioms AMSPhysical.globalSL2Recoupling_eq
