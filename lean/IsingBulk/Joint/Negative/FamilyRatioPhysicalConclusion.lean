import IsingBulk.Joint.Negative.FamilyPhysicalConclusion
import IsingBulk.Joint.Negative.FamilyRatioHighGeometry

/-! The complete physical compact-family obstruction for the actual complex
ratio family, with its neighboring physical frontier and side proved. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric FormFactors IsingBulk.Anisotropic
open scoped Topology

theorem negative_ratio_physical_obstruction {b : ℝ} {z₀ lam₀ : ℂ}
    {outerAmp : Coupling→ℂ}
    (F : ComplexRatioFamily (edgeParameter (b:ℂ)) outerAmp (-1) z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hprime : b∈primePhaseCosines) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,F.coupling (0,lam)∈frontier highDomain ∧
        p (F.coupling (0,lam))^2≠1) ∧
      CompactNegativePhysicalObstruction F.coupling
        (NegativeRatioFamily.particleAmplitude F) (closedBall lam₀ ρ) := by
  have hb := abs_lt_one_of_primePhaseCosines hprime
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
  exact ⟨ρ,hρ,hρF,hcenters,compact_negative_high_physical_obstruction F.coupling
    (NegativeRatioFamily.particleAmplitude F) (isCompact_closedBall _ _) hc ha hS hB
      (fun lam hl=>(hcenters lam hl).1) (fun lam hl=>(hcenters lam hl).2) hprime he hsq⟩

/-- The actual independent geometry constructs the complex-ratio family and
proves its complete physical uniform obstruction. Only initial boundary data
and the nonramified edge derivative are assumptions. -/
theorem exists_negative_high_ratio_physical_obstruction {b : ℝ} {z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (hprime : b∈primePhaseCosines)
    (he0 : edgeParameter (b:ℂ) (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z=>edgeParameter (b:ℂ) (z,lam₀*z)) z₀≠0) :
    ∃F : ComplexRatioFamily (edgeParameter (b:ℂ)) highPrefactor (-1) z₀ lam₀,
      ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
        (∀lam∈closedBall lam₀ ρ,F.coupling (0,lam)∈frontier highDomain ∧
          p (F.coupling (0,lam))^2≠1) ∧
        CompactNegativePhysicalObstruction F.coupling
          (NegativeRatioFamily.particleAmplitude F) (closedBall lam₀ ρ) := by
  obtain ⟨F⟩ := negative_high_complex_ratio_family hK hp hS hB he0 hd
  exact ⟨F,negative_ratio_physical_obstruction F hK hp hprime⟩

end
end IsingBulk.Joint.Negative
