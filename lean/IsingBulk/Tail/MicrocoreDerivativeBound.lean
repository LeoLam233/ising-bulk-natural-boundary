import IsingBulk.Tail.MicrocoreMeasure
import IsingBulk.Tail.MicrocoreIntegralTheorem
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The actual normalized original-source microcore integral and its uniform
all-order bound. The radius and real cutoff are fixed during differentiation. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.First MeasureTheory Filter Set
open scoped BigOperators Topology

def originalMicrocoreIntegral (n : ℕ) (d : LocalBranchData) (ε b : ℝ) (s : ℂ) : ℂ :=
  ((n+2).factorial:ℂ)⁻¹*∫ u : Fin (n+2) → ℝ,
    (scaledMicroCutoff (n+2) b u:ℂ)*
      sourceReducedAngularDensity (Real.exp (-d.c₀*ε)) s (fun i => u i-d.thetaB)

theorem originalMicrocoreLieDensity_support {n : ℕ} (d : LocalBranchData) (ε b : ℝ)
    (hb : 0 < b) (j : ℕ) (s : ℂ) :
    Function.support (@originalMicrocoreLieDensity n d ε b j s) ⊆ microcoreCube (n+1) b := by
  have hw := scaledMicroCutoff_tsupport_cube (n+1) b hb
  have hsupp : ∀ t ∈ (univ : Set ℂ), Function.support
      (fun u : AngularSpace n => (scaledMicroCutoff (n+1) b u:ℂ)*
        chartPullback (-d.c₀*ε) d.thetaB (@microRegularDensity (n+1)) t u) ⊆ microcoreCube (n+1) b := by
    intro t _ u hu
    have hn : scaledMicroCutoff (n+1) b u ≠ 0 := by intro hz; simp [hz] at hu
    exact hw (subset_closure hn)
  exact subset_closure.trans (iterate_lieStep_support_subset (microcoreField (-d.c₀*ε) d.thetaB) _
    isOpen_univ (microcoreCube_compact (n+1) b).isClosed hsupp j s (mem_univ s))

theorem originalMicrocoreIntegral_derivative_identity (n : ℕ) (d : LocalBranchData) (ε b : ℝ)
    (hε : 0 < ε) (hb : 0 < b) (s : ℂ)
    (hpoint : ∀ u : Fin (n+2) → ℝ, (∀ i, |u i| ≤ b) →
      MicrocoreDensityPoint (-d.c₀*ε) d.thetaB s u) (j : ℕ) :
    iteratedDeriv j (originalMicrocoreIntegral n d ε b) s =
      ((n+2).factorial:ℂ)⁻¹*
        ∫ u : Fin (n+2) → ℝ, originalMicrocoreLieDensity d ε b j s u
          ∂microcoreCoreMeasure (n+2) b := by
  let v := -d.c₀*ε
  let w := scaledMicroCutoff (n+2) b
  let G : ℂ → ℂ := fun t => ∫ u : Fin (n+2) → ℝ,
    (w u:ℂ)*chartPullback v d.thetaB (@microRegularDensity (n+2)) t u
  have hc : ∀ u ∈ microcoreCube (n+2) b, MicrocoreDensityPoint v d.thetaB s u :=
    fun u hu => hpoint u ((mem_microcoreCube b u).mp hu)
  obtain ⟨U,hU,hs,hdom⟩ := microcore_compact_parameter_domain v d.thetaB s _ (microcoreCube_compact (n+2) b) hc
  have he : originalMicrocoreIntegral n d ε b =ᶠ[𝓝 s] (fun t => ((n+2).factorial:ℂ)⁻¹*G t) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    unfold originalMicrocoreIntegral
    congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ microcoreCube (n+2) b
    · have hp := hdom t ht u hu
      have heq := micro_original_density_regular t v d.thetaB u (by dsimp [v]; nlinarith [d.c₀_pos])
        hp.1.g_pos hp.1.im_pos
      change (w u:ℂ)*sourceReducedAngularDensity (Real.exp v) t (fun i => u i-d.thetaB)=
        (w u:ℂ)*chartPullback v d.thetaB (@microRegularDensity (n+2)) t u
      rw [heq]
    · have hwz : w u=0 := by
        by_contra hn
        exact hu (scaledMicroCutoff_tsupport_cube (n+2) b hb (subset_closure hn))
      simp [w] at hwz
      simp [w,hwz]
  rw [he.iteratedDeriv_eq,iteratedDeriv_const_mul_field]
  have hid := microcore_compact_integral_iteratedDeriv v d.thetaB w (scaledMicroCutoff_smooth _ _)
    (microcoreCube_compact (n+2) b) (scaledMicroCutoff_tsupport_cube (n+2) b hb) hc j
  change iteratedDeriv j G s=_ at hid
  rw [hid]
  congr 1
  exact (microcore_integral_core_eq_full b (originalMicrocoreLieDensity d ε b j s)
    (originalMicrocoreLieDensity_support d ε b hb j s)).symm

theorem original_microcore_derivative_bound (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧
    ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
      let ε := Real.exp (-H)
      let b := microcoreRadius A c (n+2)
      ∀ j ≤ J,
        ‖iteratedDeriv j (originalMicrocoreIntegral n d ε b) (radialParameter d.theta ε)‖ ≤
          Real.exp (E*((n+2:ℕ):ℝ)^2)*(Real.sqrt b)^((n+2)^2-1) := by
  obtain ⟨A,c,E,hA,hc,hcs,hcap',hE,hbound⟩ := microcore_source_lie_integral_bound d halg hnot cap hcap J D hD
  refine ⟨A,c,E,hA,hc,hcs,hcap',hE,?_⟩
  filter_upwards [hbound] with H hH
  intro n hwindow
  dsimp only
  intro j hj
  obtain ⟨hpoint,hI⟩ := hH n hwindow
  have hb := microcoreRadius_pos A c hc (n+2) (by omega)
  rw [originalMicrocoreIntegral_derivative_identity n d _ _ (Real.exp_pos _) hb _ hpoint j,norm_mul]
  have hfac : ‖((n+2).factorial:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n+2)))
  exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans (hI j hj)

end
end IsingBulk.Tail
