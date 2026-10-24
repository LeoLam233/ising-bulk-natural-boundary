import IsingBulk.Anisotropic.NegativeCycles.HolomorphicTransport
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Support

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set Filter
open scoped BigOperators Topology

/-- The exact annular term created by a spatial cutoff. -/
def cutoffError {n : ℕ} (χ : ParameterSpace n → ℝ)
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (x : ParameterSpace n) : ℂ :=
  ∑ i : Fin (n+1), (-1:ℤ)^i.val •
    (fderiv ℝ χ x (Pi.single i 1)) •
      ω x (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))

theorem extDeriv_cutoff_apply {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ} {x : ParameterSpace n}
    (hχ : DifferentiableAt ℝ χ x) (hω : DifferentiableAt ℝ ω x) :
    extDeriv (fun y => χ y • ω y) x (fun k => (Pi.single k (1:ℝ) : ParameterSpace n))=
      χ x • extDeriv ω x (fun k => (Pi.single k (1:ℝ) : ParameterSpace n))+cutoffError χ ω x := by
  let e : Fin (n+1) → ParameterSpace n := fun k => Pi.single k 1
  rw [extDeriv_apply (show DifferentiableAt ℝ (fun y => χ y • ω y) x from hχ.smul hω) e]
  change (∑ i, (-1:ℤ)^i.val • fderiv ℝ (fun y => χ y • ω y (i.removeNth e)) x (e i))=_
  have hd (i : Fin (n+1)) := fderiv_fun_smul hχ
    ((hω.hasFDerivAt.continuousAlternatingMap_apply_const (i.removeNth e)).differentiableAt)
  simp_rw [hd,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_add]
  rw [Finset.sum_add_distrib,extDeriv_apply hω,Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

/-- Outside the cutoff support the weighted form is locally zero, even when
its unweighted representative is not defined analytically there. -/
theorem cutoff_form_eventually_zero {n : ℕ} {χ : ParameterSpace n → ℝ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    {x : ParameterSpace n} (hx : x∉tsupport χ) :
    (fun y => χ y • ω y)=ᶠ[𝓝 x] 0 := by
  filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
  change χ y • ω y=0
  rw [image_eq_zero_of_notMem_tsupport hy]
  exact zero_smul ℝ (ω y)

end IsingBulk.Anisotropic.NegativeCycles
