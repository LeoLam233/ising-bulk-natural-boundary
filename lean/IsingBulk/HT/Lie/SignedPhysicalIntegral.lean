import IsingBulk.HT.Lie.SignedIntegral
import IsingBulk.HT.Contour.SignedChartBridge
import IsingBulk.Tail.AllBranchExteriorAnalyticDomain

/-! Literal signed physical source correspondence, including the one outside
factorial. The cutoff remains a fixed real function through differentiation. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail
open IsingBulk.HT.Contour MeasureTheory Set Filter Function
open scoped ContDiff Topology

/-- The actual original angular density with its outside factorial. -/
def signedOriginalWeightedIntegral (σ : ℂ) (n : ℕ) (d : LocalBranchData) (ε : ℝ)
    (w : AngularSpace n → ℝ) (s : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
    (w u:ℂ)*signedSourceAngularDensity σ (Real.exp (-d.c₀*ε)) s
      (fun i => u i-d.thetaB)

theorem signed_initial_source_identity {n : ℕ} (σ : ℂ) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (s : ℂ) (u : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (u i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (u i)).im) :
    signedInitialSourceDensity σ v θ w
      (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) s u =
      (w u:ℂ)*signedSourceAngularDensity σ (Real.exp v) s (fun i => u i-θ) := by
  have he : (fun t φ => unfactoredNumerator
      (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2) (t,φ)/
        signedRegularKernel σ t φ)=(@signedMicroRegularDensity (n+1) σ) := by
    funext t φ
    rw [allBranchExterior_unfactored_eq]
    exact (signedMicroRegularDensity_unfactored σ t φ).symm
  rw [signedInitialSourceDensity,he,
    ← signed_micro_original_density_regular σ s v θ u hv hg hi]

/-- The physical differentiated integral is the actual finite Lie source sum;
all intermediate divergence integrals vanish by constructed compact support. -/
theorem signed_physical_compact_source_derivative {n : ℕ} (σ : ℂ)
    (d : LocalBranchData) (ε : ℝ) (hε : 0 < ε) (p q : Fin (n+1)) (hpq : p ≠ q)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w) (hK : HasCompactSupport w) (s : ℂ)
    (hp : ∀ u∈tsupport w, ActualJetPoint (-d.c₀*ε) d.thetaB p q s u)
    (hQ : ∀ u∈tsupport w, AnalyticAt ℂ
      (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
      (s,chartMap (-d.c₀*ε) d.thetaB s u))
    (hσ : ∀ u∈tsupport w, signedRegularKernel σ s (chartMap (-d.c₀*ε) d.thetaB s u) ≠ 0)
    (j : ℕ) :
    iteratedDeriv j (signedOriginalWeightedIntegral σ n d ε w) s =
      ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
        signedSourceTermSum σ p q (-d.c₀*ε) d.thetaB w
          (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j s u := by
  let v := -d.c₀*ε
  let Q := unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)
  have hv : v < 0 := by dsimp [v]; nlinarith [d.c₀_pos]
  have hm (u : AngularSpace n) (hu : u∈tsupport w) : MicrocoreJetPoint v d.thetaB s u :=
    ⟨(hp u hu).s_ne,(hp u hu).re_pos,(hp u hu).im_pos,(hp u hu).g_pos,(hp u hu).sin_ne,(hp u hu).slit⟩
  have hnear : ∀ᶠ t in 𝓝 s, ∀ u∈tsupport w, MicrocoreJetPoint v d.thetaB t u :=
    hK.eventually_forall_of_forall_eventually (fun u hu =>
      (microcore_joint_chart_continuous v d.thetaB s u (hm u hu)).2)
  have he : signedOriginalWeightedIntegral σ n d ε w =ᶠ[𝓝 s]
      (fun t => ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
        signedInitialSourceDensity σ v d.thetaB w Q t u) := by
    filter_upwards [hnear] with t ht
    unfold signedOriginalWeightedIntegral
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    by_cases hu : u∈tsupport w
    · exact (signed_initial_source_identity σ v d.thetaB w t u hv
        (ht u hu).g_pos (ht u hu).im_pos).symm
    · have hw0 : w u=0 := by
        by_contra hn
        exact hu (subset_tsupport w hn)
      simp [signedInitialSourceDensity,hw0]
  rw [he.iteratedDeriv_eq,iteratedDeriv_const_mul_field]
  congr 1
  exact signed_compact_integral_sourceTermSum σ v d.thetaB hv p q hpq Q w hw hK
    (Subset.refl _) hp hQ hσ j

/-- The signed source is analytic even on selected and full collision loci. -/
theorem signed_density_analytic_of_micro {n : ℕ} (σ : ℂ) (v θ : ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (u : AngularSpace n)
    (h : MicrocoreJetPoint v θ s u) (hQ : AnalyticAt ℂ Q (s,chartMap v θ s u))
    (hσ : signedRegularKernel σ s (chartMap v θ s u) ≠ 0) :
    AnalyticAt ℂ (signedComplexDensity σ v θ Q) (realAngularEmbedding (s,u)) :=
  microComplexPullback_analytic v θ _ _ h.s_ne h.re_pos h.im_pos h.sin_ne
    (hQ.div (signedRegularKernel_analytic σ _ h.s_ne h.slit) hσ)

/-- A common parameter neighborhood for all fixed spatial weights is derived
from the compact physical chart, not assumed as a derivative-exchange premise. -/
theorem signed_compact_density_domain {n : ℕ} (σ : ℂ) (v θ : ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ)
    (K : Set (AngularSpace n)) (hK : IsCompact K)
    (hp : ∀ u∈K, MicrocoreJetPoint v θ s u)
    (hQ : ∀ u∈K, AnalyticAt ℂ Q (s,chartMap v θ s u))
    (hσ : ∀ u∈K, signedRegularKernel σ s (chartMap v θ s u) ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ s∈U ∧ ∀ t∈U, ∀ u∈K,
      MicrocoreJetPoint v θ t u ∧
      AnalyticAt ℂ (signedComplexDensity σ v θ Q) (realAngularEmbedding (t,u)) := by
  have he (u : AngularSpace n) (hu : u∈K) :
      ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,u),
        MicrocoreJetPoint v θ z.1 z.2 ∧
        AnalyticAt ℂ (signedComplexDensity σ v θ Q) (realAngularEmbedding z) := by
    have hc := (microcore_joint_chart_continuous v θ s u (hp u hu)).2
    have ha := signed_density_analytic_of_micro σ v θ Q s u (hp u hu) (hQ u hu) (hσ u hu)
    have hF := (realAngularEmbedding_contDiff (n+1)).continuous.continuousAt.eventually ha.eventually_analyticAt
    exact hc.and hF
  have hall : ∀ᶠ t in 𝓝 s, ∀ u∈K,
      MicrocoreJetPoint v θ t u ∧
      AnalyticAt ℂ (signedComplexDensity σ v θ Q) (realAngularEmbedding (t,u)) :=
    hK.eventually_forall_of_forall_eventually he
  obtain ⟨U,hsub,hU,hs⟩ := mem_nhds_iff.mp hall
  exact ⟨U,hU,hs,fun t ht => hsub ht⟩

end
end IsingBulk.HT.Lie
