import StandardBentPairHighest

set_option autoImplicit false
noncomputable section
namespace AMSPhysical

theorem standardBentPairHighest_at_target (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ)
    (r:Fin (min d c+1)) (a b:ℕ) (s:Fin (min a b+1)) (L:ℕ)
    (hr:coupledLabel d c r=L) (hs:coupledLabel a b s=L):
    standardBentPairHighest q hq hq1 d c r a b s L hr hs=
      standardBentPairHighest q hq hq1 d c r a b s (coupledLabel a b s) (hr.trans hs.symm) rfl := by
  rcases hs with rfl
  rfl

end AMSPhysical
#print axioms AMSPhysical.standardBentPairHighest_at_target
