import IsingBulk.Joint.Negative.FamilyRatioHighGeometry
import IsingBulk.Joint.Negative.FamilyPhysicalJets

/-! The actual constructed complex-ratio polydisk has a common physical
negative-side approach, and the complete physical derivative sum converges
uniformly in its complex parameter. Nearby frontier membership is proved. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric FormFactors
open scoped Topology
set_option maxHeartbeats 1600000

/-- Physical, not merely formal, compact-family boundary attachment for the
actual complex-ratio chart. A single shrinking of the complex parameter disk
precedes every derivative order and every parameter. -/
theorem negative_ratio_weighted_physical_boundary_jets {b : ℝ} {z₀ lam₀ : ℂ}
    {outerAmp : Coupling→ℂ}
    (F : ComplexRatioFamily (edgeParameter (b:ℂ)) outerAmp (-1) z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,F.coupling (0,lam)∈frontier highDomain ∧
        p (F.coupling (0,lam))^2≠1) ∧
      (∃r : ℝ,0<r ∧ ∀lam∈closedBall lam₀ ρ,∀ε : ℝ,0<ε → ε<r →
        F.coupling (-(ε:ℂ),lam)∈highDomain) ∧
      ∀j : ℕ,TendstoUniformlyOn
        (fun ε : ℝ=>fun lam=>iteratedDeriv j
          (weightedPhysicalHigh (fun t=>F.coupling (t,lam))
            (fun t=>NegativeRatioFamily.particleAmplitude F (t,lam))) (-(ε:ℂ)))
        (fun lam=>∑'n : ℕ,iteratedDeriv j
          (fun t=>NegativeRatioFamily.particleAmplitude F (t,lam)^(2*n+1)*
            continuedAngularCoefficient (2*n) (F.coupling (t,lam))) 0)
        (𝓝[>] 0) (closedBall lam₀ ρ) := by
  obtain ⟨ρ,hρ,hρF,hcenters⟩ := negative_ratio_common_high_centers F hK hp hb
  have hsub : closedBall lam₀ ρ⊆closedBall lam₀ F.radius := closedBall_subset_closedBall hρF
  have hc (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) : AnalyticAt ℂ F.coupling (0,lam) :=
    F.coupling_analytic 0 lam (F.polydisk_bounds (F.zero_mem_polydisk (hsub hl))).1
      (F.polydisk_bounds (F.zero_mem_polydisk (hsub hl))).2
  have ha (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) :
      AnalyticAt ℂ (NegativeRatioFamily.particleAmplitude F) (0,lam) :=
    NegativeRatioFamily.particleAmplitude_analyticOnNhd F _ (F.zero_mem_polydisk (hsub hl))
  have hS (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) : S (F.coupling (0,lam))≠0 :=
    F.scale_ne_zero (F.zero_mem_polydisk (hsub hl))
  have hB (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) :
      (transferB (F.coupling (0,lam))).im<0 := by
    simpa only [neg_one_mul,neg_pos,ComplexRatioFamily.anisotropy] using
      F.anisotropy_sign (F.zero_mem_polydisk (hsub hl))
  have he (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) : ∀ᶠt : ℂ in 𝓝 0,
      transferC (F.coupling (t,lam))+transferB (F.coupling (t,lam))=
        (b:ℂ)+transferB (F.coupling (t,lam))*t := by
    filter_upwards [ball_mem_nhds (0:ℂ) F.radius_pos] with t ht
    exact (negative_ratio_actual_chart F
      ⟨mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp ht).le,hsub hl⟩).2.2.1
  have hsq (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) : ∀ᶠt : ℂ in 𝓝 0,
      NegativeRatioFamily.particleAmplitude F (t,lam)^2=p (F.coupling (t,lam)) := by
    filter_upwards [ball_mem_nhds (0:ℂ) F.radius_pos] with t ht
    exact NegativeRatioFamily.particleAmplitude_sq F
      ⟨mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp ht).le,hsub hl⟩
  obtain ⟨r,hr,htube⟩ := compact_negative_high_real_approach F.coupling
    (isCompact_closedBall _ _) hc hS hB (fun lam hl=>(hcenters lam hl).1)
      (fun lam hl=>(hcenters lam hl).2) hb he
  refine ⟨ρ,hρ,hρF,hcenters,⟨r,hr,fun lam hl ε hε hεr=>(htube lam hl ε hε hεr).2.2⟩,?_⟩
  exact compact_negative_high_weighted_boundary_jets F.coupling
    (NegativeRatioFamily.particleAmplitude F) (isCompact_closedBall _ _) hc ha hS hB
      (fun lam hl=>(hcenters lam hl).1) (fun lam hl=>(hcenters lam hl).2) hb he hsq

end
end IsingBulk.Joint.Negative
