import IsingBulk.Anisotropic.RegularEdges.ResolventJets
import Mathlib.Analysis.Complex.Liouville

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Tail

 theorem edgeParamRoot_uniform_derivatives {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ u : ℂ, ‖u‖<δ →
      ∀ q ∈ Icc (-Real.pi) Real.pi,
        AnalyticAt ℂ (fun v => edgeParamRoot b B v q) u ∧
        ∀ j : ℕ, ‖iteratedFDeriv ℂ j (fun v => edgeParamRoot b B v q) u‖≤
          (j.factorial:ℝ)*2/δ^j := by
  have hn : ∀ᶠ u in 𝓝 (0:ℂ), ∀ q ∈ Icc (-Real.pi) Real.pi,
      ‖edgeParamRoot b B u q‖<2 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro q _
    have hcq := edgeParamRoot_continuousAt b hc.continuousAt
      (show edgeParamW b B 0 q∈continuedRootDomain by simpa using edgeW_domain hb hB q)
    apply hcq.norm.eventually_lt continuousAt_const
    have hh := (edgeRoot_bounds hb hB q).1
    simpa only [edgeParamRoot_zero] using hh.trans_lt (by norm_num : (1:ℝ)<2)
  have hd := edgeParamW_uniform_domain hb hB hc.continuousAt
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hn.and hd).and hc.eventually_analyticAt)
  refine ⟨ε/3,by positivity,?_⟩
  intro u hu q hq
  have hsub : closedBall u (ε/3) ⊆ ball (0:ℂ) ε := by
    intro w hw
    have hwu : dist w u≤ε/3 := hw
    have hu0 : dist u 0<ε/3 := by simpa using hu
    have ht := dist_triangle w u 0
    change dist w 0<ε
    linarith
  have ha (w : ℂ) (hw : w∈ball (0:ℂ) ε) :
      AnalyticAt ℂ (fun v => edgeParamRoot b B v q) w :=
    edgeParamRoot_analyticAt b (hball hw).2 ((hball hw).1.2 q hq)
  refine ⟨ha u (by simpa using hu.trans (by linarith : ε/3<ε)),?_⟩
  intro j
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by positivity)
  · apply DifferentiableOn.diffContOnCl_ball (U := ball (0:ℂ) ε) _ hsub
    exact fun w hw => (ha w hw).differentiableAt.differentiableWithinAt
  · intro w hw
    exact ((hball (hsub (sphere_subset_closedBall hw))).1.1 q hq).le

 theorem edgeParamRoot_inward_geometric_jets {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) (J : ℕ) :
    ∃ δ M : ℝ, 0<δ ∧ 1≤M ∧ ∀ u : ℂ, ‖u‖<δ → 0<u.im →
      ∀ q ∈ Icc (-Real.pi) Real.pi,
        AnalyticAt ℂ (fun v => edgeParamRoot b B v q) u ∧
        ∀ k≤J, ‖iteratedFDeriv ℂ k (fun v => edgeParamRoot b B v q) u‖≤M^k := by
  obtain ⟨δ,hδ,hj⟩ := edgeParamRoot_uniform_derivatives hb hB hc
  obtain ⟨c,hcpos,hgap⟩ := edgeParamRoot_uniform_gap (b := b) hB hc.continuousAt
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp hgap
  let M : ℝ := 1+∑ k ∈ Finset.range (J+1), (k.factorial:ℝ)*2/δ^k
  have hterm (k : ℕ) : 0≤(k.factorial:ℝ)*2/δ^k := by positivity
  have hM : 1≤M := by dsimp [M]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hterm k)
  refine ⟨min δ η,M,lt_min hδ hη,hM,?_⟩
  intro u hu him q hq
  have hh := hj u (hu.trans_le (min_le_left _ _)) q hq
  refine ⟨hh.1,?_⟩
  intro k hk
  by_cases hk0 : k=0
  · subst k
    have hg := hηball (show u∈ball (0:ℂ) η by simpa using hu.trans_le (min_le_right _ _)) q hq him
    have hnonneg : 0≤c*(u.im+q^2) := by positivity
    simpa using (show ‖edgeParamRoot b B u q‖≤1 by linarith)
  · have hsum := Finset.single_le_sum (fun i (_ : i∈Finset.range (J+1)) => hterm i)
      (show k∈Finset.range (J+1) from Finset.mem_range.mpr (by omega))
    have hle : (k.factorial:ℝ)*2/δ^k≤M := by dsimp [M]; linarith
    exact (hh.2 k).trans (hle.trans (by simpa using pow_le_pow_right₀ hM (show 1≤k by omega)))

end IsingBulk.Anisotropic.RegularEdges
