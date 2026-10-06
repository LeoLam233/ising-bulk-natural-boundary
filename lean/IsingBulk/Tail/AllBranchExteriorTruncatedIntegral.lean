import IsingBulk.Tail.AllBranchExteriorTruncatedDomain
import IsingBulk.Tail.SourceJetIntegralTheorem
import IsingBulk.Tail.MicrocoreDomain

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter Function
open scoped ContDiff Topology

def allBranchOriginalWeightedIntegral (n : ℕ) (d : LocalBranchData) (ε : ℝ)
    (w : AngularSpace n → ℝ) (s : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
    (w u:ℂ)*sourceReducedAngularDensity (Real.exp (-d.c₀*ε)) s (fun i => u i-d.thetaB)

theorem allBranchExterior_initial_source_identity {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (s : ℂ) (u : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (u i)).re) (hi : ∀ i, 0 < (chartW s v θ (u i)).im) :
    initialSourceDensity v θ w
      (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) s u =
      (w u:ℂ)*sourceReducedAngularDensity (Real.exp v) s (fun i => u i-θ) := by
  have he : (fun t φ => unfactoredNumerator
      (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2) (t,φ)/regularKernel t φ)=
      (@microRegularDensity (n+1)) := by
    funext t φ
    rw [allBranchExterior_unfactored_eq]
    exact (microRegularDensity_unfactored t φ).symm
  rw [initialSourceDensity,he,← micro_original_density_regular s v θ u hv hg hi]

theorem allBranchExterior_compact_source_derivative {n : ℕ} (d : LocalBranchData) (ε : ℝ)
    (hε : 0 < ε) (p q : Fin (n+1)) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (hK : HasCompactSupport w) (s : ℂ)
    (hp : ∀ u ∈ tsupport w, ActualJetPoint (-d.c₀*ε) d.thetaB p q s u)
    (hQ : ∀ u ∈ tsupport w, AnalyticAt ℂ
      (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
      (s,chartMap (-d.c₀*ε) d.thetaB s u)) (j : ℕ) :
    iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε w) s =
      ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
        ((lieStep (actualField (-d.c₀*ε) d.thetaB p q))^[j]
          (initialSourceDensity (-d.c₀*ε) d.thetaB w
            (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)))) s u := by
  let v := -d.c₀*ε
  let Q := unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)
  have hv : v < 0 := by dsimp [v]; nlinarith [d.c₀_pos]
  have hm (u : AngularSpace n) (hu : u ∈ tsupport w) : MicrocoreJetPoint v d.thetaB s u :=
    ⟨(hp u hu).s_ne,(hp u hu).re_pos,(hp u hu).im_pos,(hp u hu).g_pos,(hp u hu).sin_ne,(hp u hu).slit⟩
  have hnear : ∀ᶠ t in 𝓝 s, ∀ u ∈ tsupport w, MicrocoreJetPoint v d.thetaB t u :=
    hK.eventually_forall_of_forall_eventually (fun u hu =>
      (microcore_joint_chart_continuous v d.thetaB s u (hm u hu)).2)
  have he : allBranchOriginalWeightedIntegral n d ε w =ᶠ[𝓝 s]
      (fun t => ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n, initialSourceDensity v d.thetaB w Q t u) := by
    filter_upwards [hnear] with t ht
    unfold allBranchOriginalWeightedIntegral
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    by_cases hu : u ∈ tsupport w
    · exact (allBranchExterior_initial_source_identity v d.thetaB w t u hv (ht u hu).g_pos (ht u hu).im_pos).symm
    · have hw0 : w u=0 := by
        by_contra hn
        exact hu (subset_tsupport w hn)
      simp [initialSourceDensity,hw0]
  rw [he.iteratedDeriv_eq,iteratedDeriv_const_mul_field]
  congr 1
  exact source_compact_integral_iteratedDeriv v d.thetaB p q Q w hw hK (Subset.refl _) hp hQ j

theorem allBranchExterior_truncated_derivative_identity (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n M : ℕ,
      ∀ p q : Fin (n+1), ∀ h : ℝ, 0 < h → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      let W := allBranchTruncatedWeight M h p q w
      iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε W) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
          ((lieStep (actualField (-d.c₀*ε) d.thetaB p q))^[j]
            (initialSourceDensity (-d.c₀*ε) d.thetaB W
              (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))))
            (radialParameter d.theta ε) u := by
  obtain ⟨r,hr,hdata⟩ := allBranchExterior_truncated_source_data d
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n M p q h hh w hw hsupp j
  obtain ⟨hsmooth,hcompact,hpoint⟩ := hdata ε hε hεr n M p q h hh w hw hsupp
  exact allBranchExterior_compact_source_derivative d ε hε p q _ hsmooth hcompact _
    (fun u hu => (hpoint u hu).1) (fun u hu => (hpoint u hu).2) j

end
end IsingBulk.Tail
