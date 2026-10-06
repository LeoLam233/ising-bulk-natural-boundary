import IsingBulk.Tail.RootInflation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Uniform fixed-dimensional analytic jet bounds on a compact tube.
This lemma is used only for scalar analytic phase models, never to claim
that a real deformation bump has an analytic continuation. -/
namespace IsingBulk.Tail
noncomputable section
open Set Metric
open scoped Topology BigOperators

 theorem compact_analytic_jet_bounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [ProperSpace E] (f : E → ℂ) {K : Set E}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) (k : ℕ) :
    ∃ r B : ℝ, 0<r ∧ 0<B ∧ ∀ x₀ ∈ K, ∀ x : E, ‖x-x₀‖≤r → ∀ j≤k,
      ‖iteratedFDeriv ℂ j f x‖≤B ∧
      ‖iteratedFDeriv ℂ j f x-iteratedFDeriv ℂ j f x₀‖≤B*‖x-x₀‖ := by
  let U := {x : E | AnalyticAt ℂ f x}
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open hU hf
  obtain ⟨r',hr',hcompact⟩ := hK.exists_isCompact_cthickening
  let a := min r r'
  let K' := cthickening a K
  have ha : 0<a := lt_min hr hr'
  have hK' : IsCompact K' := hcompact.of_isClosed_subset isClosed_cthickening
    (cthickening_mono (min_le_right r r') K)
  have hanalytic : AnalyticOnNhd ℂ f K' := fun x hx =>
    hsub ((cthickening_mono (min_le_left r r') K) hx)
  have hjet (j : ℕ) : ∃ B : ℝ, 0<B ∧
      (∀ x ∈ K', ‖iteratedFDeriv ℂ j f x‖≤B) ∧
      (∀ x ∈ K', ∀ y ∈ K', ‖iteratedFDeriv ℂ j f x-iteratedFDeriv ℂ j f y‖≤B*‖x-y‖) := by
    have hj := hanalytic.iteratedFDeriv j
    have hc : ContinuousOn (iteratedFDeriv ℂ j f) K' := fun x hx => (hj x hx).continuousAt.continuousWithinAt
    obtain ⟨M,hM⟩ := hK'.exists_bound_of_continuousOn hc
    have hlocal : LocallyLipschitzOn K' (iteratedFDeriv ℂ j f) := by
      intro x hx
      have hd : ContDiffAt ℂ 1 (iteratedFDeriv ℂ j f) x := (hj x hx).contDiffAt
      obtain ⟨A,T,hT,hAT⟩ := hd.exists_lipschitzOnWith
      exact ⟨A,T,mem_nhdsWithin_of_mem_nhds hT,hAT⟩
    obtain ⟨A,hA⟩ := hlocal.exists_lipschitzOnWith_of_compact hK'
    let B := max M (A:ℝ)+1
    have hB : 0<B := by dsimp [B]; have hh := le_max_right M (A:ℝ); positivity
    have hMB : M≤B := (le_max_left M (A:ℝ)).trans (by dsimp [B]; linarith)
    have hAB : (A:ℝ)≤B := (le_max_right M (A:ℝ)).trans (by dsimp [B]; linarith)
    refine ⟨B,hB,fun x hx => (hM x hx).trans hMB,?_⟩
    intro x hx y hy
    exact (hA.norm_sub_le hx hy).trans (mul_le_mul_of_nonneg_right hAB (norm_nonneg _))
  choose B hB hb hl using hjet
  let C := 1+∑ j ∈ Finset.range (k+1), B j
  have hC : 0<C := by
    have hh : 0≤∑ j ∈ Finset.range (k+1), B j := Finset.sum_nonneg (fun j _ => (hB j).le)
    dsimp [C]
    linarith
  refine ⟨a,C,ha,hC,?_⟩
  intro x₀ hx₀ x hx j hj
  have hx₀' : x₀ ∈ K' := self_subset_cthickening K hx₀
  have hx' : x ∈ K' := mem_cthickening_of_dist_le x x₀ a K hx₀ (by simpa [dist_eq_norm] using hx)
  have hBC : B j≤C := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.range (k+1)) => (hB l).le)
      (show j∈Finset.range (k+1) from Finset.mem_range.mpr (by omega))
    dsimp [C]
    linarith
  exact ⟨(hb j x hx').trans hBC,(hl j x hx' x₀ hx₀').trans
    (mul_le_mul_of_nonneg_right hBC (norm_nonneg _))⟩

end
end IsingBulk.Tail
