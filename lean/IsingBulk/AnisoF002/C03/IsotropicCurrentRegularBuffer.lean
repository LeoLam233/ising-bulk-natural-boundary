import IsingBulk.AnisoF002.C03.IsotropicTransportDensity
import IsingBulk.AnisoF002.C03.IsotropicCurrentBuffer

/-!
# The entire actual current, smooth and parameter-holomorphic

One fixed geometric angular buffer is chosen before the smooth bump
width. Every full transported density is smooth off total coincidence,
holomorphic in the physical parameter at fixed real angles, and obeys
the original eliminated-anchor current identity on the same domain.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators ContDiff

theorem exists_actual_complete_current_regular_buffer (S : ℝ)
    (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β) β) →
        ∀ i l, θ i ≠ θ l → ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ∀ (g : (Fin N → ℝ) → ℂ), ContDiff ℝ ∞ g → ∀ j : ℕ,
        ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g j) (s, θ) ∧
          AnalyticAt ℂ (fun u => actualTransportedDensity σ η τ ξ g j (u, θ)) s ∧
          (∀ k, DifferentiableAt ℝ (actualTransportedFlux σ η τ ξ g j k) (s, θ)) ∧
          ∀ anchor : Fin N,
            scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection (s, θ) -
              (∑ k ∈ Finset.univ.erase anchor,
                scalarPartial (actualTransportedFlux σ η τ ξ g j k)
                  (actualAngularDirection k - actualAngularDirection anchor) (s, θ)) =
              actualTransportedDensity σ η τ ξ g (j + 1) (s, θ) := by
  obtain ⟨βF, hβF, hβF1, hframe⟩ := exists_actual_physical_frame_buffer S hS
  obtain ⟨βB, hβB, _, hcov⟩ := exists_actual_right_covariance_transport_buffer S hS
  obtain ⟨βC, hβC, _, hcurrent⟩ := exists_actual_complete_density_current_buffer S hS
  obtain ⟨βV, hβV, _, hvelocity⟩ := exists_actual_right_smooth_current_buffer S hS
  obtain ⟨r, _, _, _, hr, _, _, _, hnum⟩ :=
    exists_actual_oneSided_retainedNumerator_analytic_gaussian S hS
  obtain ⟨δI, hδI, himage⟩ := exists_actual_oneSided_homotopy_domain S r hS hr
  let β := min βF (min βB (min βC (min βV δI)))
  have hβ : 0 < β := by dsimp [β]; positivity
  have hbF : β ≤ βF := min_le_left _ _
  have hbB : β ≤ βB := (min_le_right _ _).trans (min_le_left _ _)
  have hbC : β ≤ βC := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbV : β ≤ βV := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hbI : β ≤ δI := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨β, hβ, hbF.trans hβF1, ?_⟩
  intro η hη
  obtain ⟨δF, hδF, _, hinv, hf⟩ := hframe η hη
  obtain ⟨δB, hδB, _, hb⟩ := hcov η hη
  obtain ⟨δC, hδC, _, hc⟩ := hcurrent η hη
  obtain ⟨δV, hδV, _, hv⟩ := hvelocity η hη
  let δ := min β (min δF (min δB (min δC δV)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdF : δ ≤ δF := (min_le_right _ _).trans (min_le_left _ _)
  have hdB : δ ≤ δB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC : δ ≤ δC := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdV : δ ≤ δV := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hdI : δ ≤ δI := hdβ.trans hbI
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN s hs hsd τ hτ ξ hξ θ hθ i l hil σ hσ g hg j
  let q : ℂ × (Fin N → ℝ) := (s, θ)
  let p := regularJointMap (actualPhysicalCoordinate η τ ξ) q
  have hθF : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - βF) βF :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbF⟩
  have hθB : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - βB) βB :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbB⟩
  have hθC : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - βC) βC :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbC⟩
  have hθV : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - βV) βV :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbV⟩
  have hθI : ∀ k, θ k ∈ Icc (-Real.pi - δI) δI :=
    fun k => ⟨by linarith [(hθ k).1, rightBranchEndpoint_lt_pi S hS.1], (hθ k).2.trans hbI⟩
  obtain ⟨hχ, hdet, hU, hVgerm⟩ := hf N hN s hs (hsd.trans_le hdF) τ ξ
    ⟨hτ.1, hτ.2.trans hdF⟩ hξ θ hθF
  have hBa := (hb N hN s hs (hsd.trans_le hdB) τ ⟨hτ.1, hτ.2.trans hdB⟩ ξ hξ θ hθB i l hil).1
  have hKa (k : Fin N) : AnalyticAt ℂ (fun z : RegularJointSpace N => rightCutoffTransportCoefficient z k) p :=
    rightCutoffTransportCoefficient_analyticAt p k (hU k) hBa
  have hp := (himage N hN s hs (hsd.trans_le hdI) η τ ξ hη
    ⟨hτ.1, hτ.2.trans hdI⟩ hξ θ hθI).1
  have hFa := (hnum N ∅ (Finset.empty_subset _) _ hp).1
  rw [retainedRegularNumerator_empty] at hFa
  let F : RegularJointSpace N → ℂ := fun z => isotropicParticleNormalization N * completeRegularNumerator N z
  have hF : AnalyticAt ℂ F p := analyticAt_const.mul hFa
  have hA (k m : Fin N) : ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ k m) := by
    apply contDiff_infty.mpr
    intro z
    obtain ⟨Cz, _, hz⟩ := hinv z
    exact (hz N hN τ ξ ⟨hτ.1, hτ.2.trans hdF⟩ hξ k m).smooth
  have hinit : actualInitialAmplitude η τ ξ (fun y : ℂ × (Fin N → ℝ) => g y.2) =
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) := by
    funext y
    change isotropicParticleNormalization N * g y.2 * completeRegularNumerator N _ =
      (isotropicParticleNormalization N * completeRegularNumerator N _) * g y.2
    dsimp only [regularJointMap]
    ring
  have hba : AnalyticAt ℂ (fun u => actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j (u, θ)) s := by
    rw [hinit]
    exact actualTransportDescendant_parameter_analyticAt η τ ξ F g hA hg θ s hη hτ.1 hξ.1 hs
      hχ hBa hKa hF hdet hVgerm j
  have hcut : ContDiffAt ℝ ∞ (fun y : ℂ × (Fin N → ℝ) => g y.2) q :=
    hg.contDiffAt.comp q contDiffAt_snd
  have hcurrent' (anchor : Fin N) := hc N hN s hs (hsd.trans_le hdC) τ
    ⟨hτ.1, hτ.2.trans hdC⟩ ξ hξ θ hθC i l hil anchor σ hσ (fun y => g y.2) hcut j
  let anchor : Fin N := ⟨0, hN⟩
  have hbs := (hcurrent' anchor).1
  have hms := actualTransportDensityMultiplier_interior_smooth hN σ hσ η τ ξ hη hτ.1 hξ.1 q hs
  have hds : ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g j) q := hms.mul hbs
  have hVs := (hv N hN s hs (hsd.trans_le hdV) τ ⟨hτ.1, hτ.2.trans hdV⟩ ξ hξ θ hθV i l hil).2.2.2.1
  refine ⟨hds, ?_, fun k => (hVs k).mul (hds.differentiableAt (by simp)), ?_⟩
  · exact (actualTransportDensityMultiplier_parameter_analyticAt hN σ hσ η τ ξ θ s hη hτ.1 hξ.1 hs).mul hba
  · intro a
    unfold actualTransportedFlux actualTransportedDensity actualTransportDensityMultiplier
    simpa only [mul_assoc] using (hcurrent' a).2

end
end IsingBulk.AnisoF002.Isotropic
