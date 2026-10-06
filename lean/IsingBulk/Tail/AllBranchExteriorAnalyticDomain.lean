import IsingBulk.Tail.AllBranchExteriorTruncatedIntegral
import IsingBulk.Tail.BoundedWeightAnalyticIntegral

/-! Analyticity of the original all-branch density does not require a selected
pair to be distinct. This supplies the compact parameter neighborhood used to
remove the pair cutoff, including the collision locus. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Set Filter
open scoped Topology ContDiff

theorem allBranchExterior_kernel_ne_zero_of_micro {n : ℕ} (v θ : ℝ) (hv : v < 0)
    (s : ℂ) (u : AngularSpace n) (h : MicrocoreJetPoint v θ s u) :
    regularKernel s (chartMap v θ s u) ≠ 0 := by
  have hy : ∀ i, ‖regularY s (chartMap v θ s u i)‖ < 1 := by
    intro i
    rw [show chartMap v θ s u i=chartPhase s v θ (u i) from rfl,
      regularY_chartPhase _ _ _ _ (h.g_pos i),angularY_norm_real,Real.exp_lt_one_iff]
    exact hv
  have hz : ∀ i, ‖Complex.exp (-Complex.I*chartMap v θ s u i)‖ < 1 := by
    intro i
    rw [show chartMap v θ s u i=chartPhase s v θ (u i) from rfl,← chart_root_eq_physical]
    exact interiorRoot_norm_lt_one (h.im_pos i)
  apply mul_ne_zero
  · exact one_sub_coordinateProduct_ne_zero (by omega) hy
  · rw [regularZProduct_eq_prod]
    exact one_sub_coordinateProduct_ne_zero (by omega) hz

theorem allBranchExterior_density_analytic_of_micro {n : ℕ} (v θ : ℝ) (hv : v < 0)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (u : AngularSpace n)
    (h : MicrocoreJetPoint v θ s u) (hQ : AnalyticAt ℂ Q (s,chartMap v θ s u)) :
    AnalyticAt ℂ (sourceComplexDensity v θ Q) (realAngularEmbedding (s,u)) :=
  microComplexPullback_analytic v θ _ _ h.s_ne h.re_pos h.im_pos h.sin_ne
    (hQ.div (regularKernel_analytic _ h.s_ne h.slit)
      (allBranchExterior_kernel_ne_zero_of_micro v θ hv s u h))

theorem allBranchExterior_original_density_data (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ,
      ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) →
        MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u ∧
        AnalyticAt ℂ
          (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
          (radialParameter d.theta ε,chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) := by
  obtain ⟨rC,hrC,hchart⟩ := original_microcore_chart d
  obtain ⟨C,rQ,_,hrQ,hnum⟩ := allBranchExterior_original_numerator_jets d 0
  let r := min rC rQ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrc : r < rC := (half_lt_self (lt_min hrC hrQ)).trans_le (min_le_left _ _)
  have hrq : r < rQ := (half_lt_self (lt_min hrC hrQ)).trans_le (min_le_right _ _)
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n u hu
  refine ⟨hchart ε hε (hεr.trans_lt hrc) n u (fun i => (hu i).trans_lt hrc),?_⟩
  simpa only [original_chartMap_eq] using
    (hnum ε hε (hεr.trans hrq.le) (n+1) u (fun i => (hu i).trans hrq.le)).analytic

theorem allBranchExterior_compact_density_domain {n : ℕ} (v θ : ℝ) (hv : v < 0)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ)
    (K : Set (AngularSpace n)) (hK : IsCompact K)
    (hp : ∀ u ∈ K, MicrocoreJetPoint v θ s u)
    (hQ : ∀ u ∈ K, AnalyticAt ℂ Q (s,chartMap v θ s u)) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ ∀ t ∈ U, ∀ u ∈ K,
      MicrocoreJetPoint v θ t u ∧
      AnalyticAt ℂ (sourceComplexDensity v θ Q) (realAngularEmbedding (t,u)) := by
  have he (u : AngularSpace n) (hu : u ∈ K) :
      ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,u),
        MicrocoreJetPoint v θ z.1 z.2 ∧
        AnalyticAt ℂ (sourceComplexDensity v θ Q) (realAngularEmbedding z) := by
    have hc := (microcore_joint_chart_continuous v θ s u (hp u hu)).2
    have ha := allBranchExterior_density_analytic_of_micro v θ hv Q s u (hp u hu) (hQ u hu)
    have hF := (realAngularEmbedding_contDiff (n+1)).continuous.continuousAt.eventually ha.eventually_analyticAt
    exact hc.and hF
  have hall : ∀ᶠ t in 𝓝 s, ∀ u ∈ K,
      MicrocoreJetPoint v θ t u ∧
      AnalyticAt ℂ (sourceComplexDensity v θ Q) (realAngularEmbedding (t,u)) :=
    hK.eventually_forall_of_forall_eventually he
  obtain ⟨U,hsub,hU,hs⟩ := mem_nhds_iff.mp hall
  exact ⟨U,hU,hs,fun t ht => hsub ht⟩

end
end IsingBulk.Tail
