import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Filter
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

def localParticleRoot (P : ℂ → ℂ) (u : ℂ) : ℂ :=
  Complex.sqrt (P 0)*Complex.sqrt (P u/P 0)

theorem localParticleRoot_sq {P : ℂ → ℂ} (hP0 : P 0≠0) (u : ℂ) :
    localParticleRoot P u^2=P u := by
  simp only [localParticleRoot,mul_pow,Complex.sqrt,Complex.cpow_ofNat_inv_pow]
  field_simp

theorem localParticleRoot_ne_zero {P : ℂ → ℂ} (hP0 : P 0≠0) :
    localParticleRoot P 0≠0 := by
  intro h
  have hh := localParticleRoot_sq hP0 0
  simp [h] at hh
  exact hP0 hh.symm

theorem localParticleRoot_analyticAt {P : ℂ → ℂ} (hP : AnalyticAt ℂ P 0) (hP0 : P 0≠0) :
    AnalyticAt ℂ (localParticleRoot P) 0 := by
  have hs : AnalyticAt ℂ Complex.sqrt (P 0/P 0) := by
    rw [div_self hP0]
    exact Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane 1 Complex.one_mem_slitPlane
  apply analyticAt_const.mul
  exact AnalyticAt.fun_comp_of_eq (f:=fun u : ℂ => P u/P 0) (g:=Complex.sqrt)
    hs hP.div_const rfl

end IsingBulk.Anisotropic.RegularEdges
