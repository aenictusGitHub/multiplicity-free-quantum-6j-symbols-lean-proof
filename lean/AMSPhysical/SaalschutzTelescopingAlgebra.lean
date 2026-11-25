import Mathlib.Tactic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def saalschutzRatio (A B C N : ℝ) : ℝ :=
  (A-C*N)*(B-C*N)/((1-C*N)*(A*B-C*N))
def saalschutzFlux (Q C N x : ℝ) : ℝ :=
  -Q*N*(1-x)*(1-C*x/Q)/(x*(C*N-1)*(Q*N-1))
def saalschutzNratio (A B C Q N x : ℝ) : ℝ :=
  (Q*N-x)*(C*N-A*B)/((Q*N-1)*(C*N-A*B*x))
def saalschutzKratio (A B C Q N x : ℝ) : ℝ :=
  Q*(1-A*x)*(1-B*x)*(1-x/(Q*N))*(C*N)/((1-Q*x)*(1-C*x)*(C*N-A*B*x))

/-- A rational telescoping certificate, independently verified by field arithmetic. -/
theorem saalschutz_telescoping_algebra (A B C Q N x U : ℝ)
    (hQ : Q≠0) (hN : N≠0) (hx : x≠0) (hCN : C*N-1≠0) (hQN : Q*N-1≠0)
    (hAB : A*B-C*N≠0) (hX : C*N-A*B*x≠0) (hQx : 1-Q*x≠0) (hCx : 1-C*x≠0) :
    U-saalschutzRatio A B C N*(U*saalschutzNratio A B C Q N x)=
      saalschutzFlux Q C N (Q*x)*(U*saalschutzKratio A B C Q N x)-saalschutzFlux Q C N x*U := by
  have hCN' : 1-C*N≠0 := by intro h;apply hCN;linarith
  unfold saalschutzRatio saalschutzNratio saalschutzKratio saalschutzFlux
  have hQN' : -1+N*Q≠0 := by intro h;apply hQN;nlinarith
  field_simp
  ring_nf
  field_simp [hQN']
  ring

end AMSPhysical

#print axioms AMSPhysical.saalschutz_telescoping_algebra
