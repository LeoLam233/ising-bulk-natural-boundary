import IsingBulk.Joint.FormFactors.CompactIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact all-order complex Fréchet differentiation through the actual compact
angular integral. The jets are derived recursively from the analytic kernel;
no derivative-exchange or jet-integrability oracle is assumed. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

variable {E V G X : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem compact_analytic_integral_iteratedFDeriv (n : ℕ)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set E} (hU : IsOpen U) (F : E × V → G) (psi : X → V) (hpsi : Continuous psi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) {s : E} (hs : s∈U) :
    iteratedFDeriv ℂ n (fun z => ∫ x in K, F (z,psi x) ∂μ) s =
      ∫ x in K, iteratedFDeriv ℂ n (fun z => F (z,psi x)) s ∂μ := by
  induction n generalizing G with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℂ E G).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ n ih =>
    have hdf : fderiv ℂ (fun z => ∫ x in K, F (z,psi x) ∂μ) =ᶠ[𝓝 s]
        (fun z => ∫ x in K, parameterFDeriv F (z,psi x) ∂μ) := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact (compact_analytic_integral_hasFDerivAt hK hU F psi hpsi hF hz).fderiv
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply]
    rw [(hdf.iteratedFDeriv ℂ n).eq_of_nhds]
    rw [ih (parameterFDeriv F) (fun z hz x hx => parameterFDeriv_analyticAt (hF z hz x hx))]
    have hcomm : (continuousMultilinearCurryRightEquiv' ℂ n E G).symm
        (∫ x in K, iteratedFDeriv ℂ n (fun z => parameterFDeriv F (z,psi x)) s ∂μ) =
        ∫ x in K, (continuousMultilinearCurryRightEquiv' ℂ n E G).symm
          (iteratedFDeriv ℂ n (fun z => parameterFDeriv F (z,psi x)) s) ∂μ := by
      simpa using! ((continuousMultilinearCurryRightEquiv' ℂ n E G).symm.toLinearIsometry.integral_comp_comm
        (μ := μ.restrict K) (fun x => iteratedFDeriv ℂ n (fun z => parameterFDeriv F (z,psi x)) s)).symm
    rw [hcomm]
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    dsimp only
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply]
    congr 1
    have he : (fun z => parameterFDeriv F (z,psi x)) =ᶠ[𝓝 s]
        fderiv ℂ (fun z => F (z,psi x)) := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact ((hF z hz x hx).differentiableAt.hasFDerivAt.comp z
        ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (psi x) z))).fderiv.symm
    exact (he.iteratedFDeriv ℂ n).eq_of_nhds

/-- Fixed shape/Jacobian weights are included inside the genuine kernel, so
all mixed jets commute with weighted angular integration as well. -/
theorem compact_analytic_shape_integral_iteratedFDeriv (n : ℕ)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set E} (hU : IsOpen U) (F : E × V → G) (psi : X → V) (hpsi : Continuous psi)
    (chi : X → ℂ) (hchi : Continuous chi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) {s : E} (hs : s∈U) :
    iteratedFDeriv ℂ n (fun z => ∫ x in K, chi x • F (z,psi x) ∂μ) s =
      ∫ x in K, iteratedFDeriv ℂ n (fun z => chi x • F (z,psi x)) s ∂μ := by
  let F' : E × (V × ℂ) → G := fun q => q.2.2 • F (q.1,q.2.1)
  have ha : ∀ z ∈ U, ∀ x ∈ K, AnalyticAt ℂ F' (z,(psi x,chi x)) := by
    intro z hz x hx
    have hmap : AnalyticAt ℂ (fun q : E × (V × ℂ) => (q.1,q.2.1))
        (z,(psi x,chi x)) :=
      analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
    have hcomp := (hF z hz x hx).comp (f := fun q : E × (V × ℂ) => (q.1,q.2.1)) hmap
    exact (analyticAt_snd.comp analyticAt_snd).smul hcomp
  exact compact_analytic_integral_iteratedFDeriv n hK hU F'
    (fun x => (psi x,chi x)) (hpsi.prodMk hchi) ha hs

end
end IsingBulk.Joint.FormFactors
