import IsingBulk.HT.Contour.SignedAngularChart
import IsingBulk.HT.Lie.SignedNearChartWindow
import IsingBulk.HT.Lie.SignedFarChartWindow
import IsingBulk.Tail.AllBranchExteriorAngularChart
import IsingBulk.Tail.AllBranchExteriorNearChartWindow
import IsingBulk.Tail.AllBranchExteriorFarChartWindow
import IsingBulk.Tail.RadialSourceDomain

/-! The original angular near/far terms, with one radial threshold for the
whole intermediate particle window. The majorant is summable in N. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.HT.Contour IsingBulk.Tail IsingBulk.First IsingBulk.Branch Filter
open scoped Topology BigOperators

def signedExteriorAngularNorm (σ : ℂ) (N : ℕ) (d : LocalBranchData)
    (η δ ε b ρ : ℝ) (hδ : 0 < δ) (j : ℕ) : ℝ :=
  ∑ v : Fin N,
    (‖iteratedDeriv j (signedMicroPartitionAngularIntegral σ N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,0))) (radialParameter d.theta ε)‖ +
    ‖iteratedDeriv j (signedMicroPartitionAngularIntegral σ N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,1))) (radialParameter d.theta ε)‖)

theorem signedExteriorAngularNorm_nonneg (σ : ℂ) (N : ℕ) (d : LocalBranchData)
    (η δ ε b ρ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    0 ≤ signedExteriorAngularNorm σ N d η δ ε b ρ hδ j := by
  unfold signedExteriorAngularNorm
  positivity

theorem signed_exterior_angular_window (α : ℝ) {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2)
    (hα : d.alpha < Real.sin d.thetaB/4) (j : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ Aμ cμ : ℝ, 0 ≤ Aμ → 0 < cμ → cμ ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      ∃ S : ℕ → ℝ, Summable S ∧ (∀ N, 0 ≤ S N) ∧
      ∀ Dwin : ℝ, 0 ≤ Dwin → ∀ᶠ H : ℝ in atTop, ∀ n : ℕ,
        (n+1:ℝ) ≤ Dwin*Real.sqrt H → 2*j+1 ≤ (n+1)*n →
        signedExteriorAngularNorm (Complex.exp (Complex.I*(α:ℂ))) (n+1) d η δ (Real.exp (-H))
          (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ j
          ≤ S (n+1)*(H+1)^2 := by
  obtain ⟨r₁,hr₁,hnear⟩ := signed_near_chart_window α B hcsmall j
  obtain ⟨r₂,hr₂,hfar⟩ := signed_far_chart_window α B hcsmall j
  let h := min r₁ (min r₂ (min (1/2:ℝ) (min (d.thetaB/2) ((Real.pi-d.thetaB)/2))))
  have hh : 0 < h := lt_min hr₁ (lt_min hr₂ (lt_min (by norm_num)
    (lt_min (half_pos d.thetaB_pos) (half_pos (sub_pos.mpr d.thetaB_lt)))))
  have hh₁ : h ≤ r₁ := min_le_left _ _
  have hh₂ : h ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hhrest : h ≤ min (1/2:ℝ) (min (d.thetaB/2) ((Real.pi-d.thetaB)/2)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hhhalf : h ≤ 1/2 := hhrest.trans (min_le_left _ _)
  have hhθ : h ≤ d.thetaB/2 := hhrest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhπ : h ≤ (Real.pi-d.thetaB)/2 := hhrest.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨δ₀,hδ₀,heq⟩ := signed_allBranchExterior_angular_chart_derivatives d h hh hhθ hhπ hα
  refine ⟨δ₀,hδ₀,?_⟩
  intro η δ hδ hδsmall Aμ cμ hAμ hcμ hcμ1
  obtain ⟨β₀,hβ₀,hnb⟩ := hnear h hh hh₁ (by linarith) hhθ hhπ η δ hδ Aμ cμ hAμ hcμ hcμ1
  refine ⟨β₀,hβ₀,?_⟩
  intro β hβ
  obtain ⟨S₁,hs₁,hS₁,hN⟩ := hnb β hβ
  obtain ⟨S₂,hs₂,hS₂,hF⟩ := hfar h hh hh₂ (by linarith) hhθ hhπ η δ hδ Aμ cμ β hAμ hcμ hcμ1
    (hβ₀.le.trans hβ)
  refine ⟨fun N => S₁ N+S₂ N,hs₁.add hs₂,fun N => add_nonneg (hS₁ N) (hS₂ N),?_⟩
  intro Dwin hDwin
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [hN Dwin hDwin,hF Dwin hDwin,
    ht.eventually (radial_source_eventually_damping d hcsmall)] with H hn hf hdom
  intro n hwindow horder
  have hnpos : 1 ≤ n := by
    by_contra hn
    have hn0 : n=0 := by omega
    simp only [hn0,mul_zero] at horder
    omega
  have hhN := hn n hwindow horder
  have hhF := hf n hnpos hwindow
  have hchange : signedExteriorAngularNorm (Complex.exp (Complex.I*(α:ℂ))) (n+1) d η δ (Real.exp (-H))
      (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ j =
      (∑ v : Fin (n+1), ‖iteratedDeriv j (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d (Real.exp (-H))
        (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h
          (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ v))
        (radialParameter d.theta (Real.exp (-H)))‖) +
      (∑ v : Fin (n+1), ‖iteratedDeriv j (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d (Real.exp (-H))
        (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h
          (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ v))
        (radialParameter d.theta (Real.exp (-H)))‖) := by
    unfold signedExteriorAngularNorm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    obtain ⟨heN,heF⟩ := heq δ hδ hδsmall (Complex.exp (Complex.I*(α:ℂ))) n η (Real.exp (-H))
      (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1))
      v _ j
    rw [heN,heF]
  rw [hchange,add_mul]
  exact add_le_add hhN hhF

end
end IsingBulk.HT.Lie
