import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

/-- One sign for an ordered fusion triple. There is no exterior quadruple
argument and no distinction according to the context in which it is used. -/
structure GlobalVertexSigns (O : Type*) where
  sign : O → O → O → ℝ
  square : ∀ a b c, sign a b c * sign a b c = 1

/-- Labels at internal nodes are the intermediate irreducible labels. -/
inductive LabelledFusionTree (O : Type*) where
  | leaf : O → LabelledFusionTree O
  | join : O → LabelledFusionTree O → LabelledFusionTree O → LabelledFusionTree O

def LabelledFusionTree.output {O : Type*} : LabelledFusionTree O → O
  | .leaf a => a
  | .join a _ _ => a

def GlobalVertexSigns.treeSign {O : Type*} (g : GlobalVertexSigns O) :
    LabelledFusionTree O → ℝ
  | .leaf _ => 1
  | .join a s t => g.sign s.output t.output a * g.treeSign s * g.treeSign t

theorem GlobalVertexSigns.treeSign_square {O : Type*} (g : GlobalVertexSigns O)
    (t : LabelledFusionTree O) : g.treeSign t * g.treeSign t = 1 := by
  induction t with
  | leaf a => simp only [treeSign, mul_one]
  | join a s t hs ht =>
    change (g.sign s.output t.output a * g.treeSign s * g.treeSign t) *
      (g.sign s.output t.output a * g.treeSign s * g.treeSign t) = 1
    calc
      _ = (g.sign s.output t.output a * g.sign s.output t.output a) *
        (g.treeSign s * g.treeSign s) * (g.treeSign t * g.treeSign t) := by ring
      _ = 1 := by rw [g.square, hs, ht]; norm_num

def GlobalVertexSigns.transitionSign {O : Type*} (g : GlobalVertexSigns O)
    (s t : LabelledFusionTree O) : ℝ := g.treeSign s * g.treeSign t

/-- The common tree sign cancels on composition. Thus one global vertex
assignment gives coherent signs along every sequence of associativity moves. -/
theorem GlobalVertexSigns.transition_comp {O : Type*} (g : GlobalVertexSigns O)
    (s t u : LabelledFusionTree O) :
    g.transitionSign s t * g.transitionSign t u = g.transitionSign s u := by
  unfold transitionSign
  calc
    _ = g.treeSign s * (g.treeSign t * g.treeSign t) * g.treeSign u := by ring
    _ = _ := by rw [g.treeSign_square, mul_one]

theorem GlobalVertexSigns.transition_cycle {O : Type*} (g : GlobalVertexSigns O)
    (s t u : LabelledFusionTree O) :
    g.transitionSign s t * g.transitionSign t u * g.transitionSign u s = 1 := by
  rw [g.transition_comp, g.transition_comp]
  exact g.treeSign_square s

def GlobalVertexSigns.recouplingSign {O : Type*} (g : GlobalVertexSigns O)
    (a b c d e f : O) : ℝ :=
  g.sign a b e * g.sign e c d * g.sign b c f * g.sign a f d

theorem GlobalVertexSigns.recouplingSign_trees {O : Type*} (g : GlobalVertexSigns O)
    (a b c d e f : O) :
    g.transitionSign (.join d (.join e (.leaf a) (.leaf b)) (.leaf c))
      (.join d (.leaf a) (.join f (.leaf b) (.leaf c))) =
      g.recouplingSign a b c d e f := by
  simp only [transitionSign, treeSign, LabelledFusionTree.output, mul_one, recouplingSign]
  ring

def GlobalVertexSigns.pathSign {O : Type*} (g : GlobalVertexSigns O)
    (s : LabelledFusionTree O) : List (LabelledFusionTree O) → ℝ
  | [] => 1
  | t :: ts => g.transitionSign s t * g.pathSign t ts

/-- Phase factors along an arbitrary finite sequence of tree changes
depend only on the endpoint trees. This includes every pentagon path. -/
theorem GlobalVertexSigns.pathSign_endpoint {O : Type*} (g : GlobalVertexSigns O)
    (path : List (LabelledFusionTree O)) (s t : LabelledFusionTree O) :
    g.pathSign s (path ++ [t]) = g.transitionSign s t := by
  induction path generalizing s with
  | nil => simp only [List.nil_append, pathSign, mul_one]
  | cons u path ih =>
    simp only [List.cons_append, pathSign]
    rw [ih, g.transition_comp]

theorem GlobalVertexSigns.pathSign_closed {O : Type*} (g : GlobalVertexSigns O)
    (path : List (LabelledFusionTree O)) (s : LabelledFusionTree O) :
    g.pathSign s (path ++ [s]) = 1 := by
  rw [g.pathSign_endpoint]
  exact g.treeSign_square s

end AMSPhysical
#print axioms AMSPhysical.GlobalVertexSigns.transition_cycle
#print axioms AMSPhysical.GlobalVertexSigns.pathSign_closed
