import IsingBulk.Joint.Negative.FamilyObstruction
import IsingBulk.Joint.Negative.FamilyActualRatio

/-! The compact-family obstruction specialized to the actual jointly analytic
complex-ratio polydisk constructed from the independent coupling geometry. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic
open FormFactors
open scoped Topology

/-- Every constructed actual complex-ratio chart has the complete common
negative-odd coefficient obstruction on its closed complex parameter disk. -/
theorem negative_ratio_family_obstruction {b : ℝ} {z₀ lam₀ : ℂ} {outerAmp : Coupling→ℂ}
    (F : ComplexRatioFamily (edgeParameter (b:ℂ)) outerAmp (-1) z₀ lam₀)
    (hprime : b∈primePhaseCosines) :
    CompactNegativeCoefficientObstruction F.coupling
      (NegativeRatioFamily.particleAmplitude F) (closedBall lam₀ F.radius) := by
  apply compact_normalized_negative_family_obstruction F.coupling
    (NegativeRatioFamily.particleAmplitude F) (isCompact_closedBall _ _)
  · intro lam hl
    exact F.coupling_analytic 0 lam (F.polydisk_bounds (F.zero_mem_polydisk hl)).1
      (F.polydisk_bounds (F.zero_mem_polydisk hl)).2
  · intro lam hl
    exact NegativeRatioFamily.particleAmplitude_analyticOnNhd F _ (F.zero_mem_polydisk hl)
  · intro lam hl
    exact F.scale_ne_zero (F.zero_mem_polydisk hl)
  · intro lam hl
    have hh := F.anisotropy_sign (F.zero_mem_polydisk hl)
    simpa only [neg_one_mul,neg_pos,ComplexRatioFamily.anisotropy] using hh
  · exact hprime
  · intro lam hl
    filter_upwards [ball_mem_nhds (0:ℂ) F.radius_pos] with t ht
    have hq : (t,lam)∈F.polydisk :=
      ⟨mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp ht).le,hl⟩
    exact (negative_ratio_actual_chart F hq).2.2.1
  · intro lam hl
    filter_upwards [ball_mem_nhds (0:ℂ) F.radius_pos] with t ht
    have hq : (t,lam)∈F.polydisk :=
      ⟨mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp ht).le,hl⟩
    exact NegativeRatioFamily.particleAmplitude_sq F hq

/-- Actual high-temperature boundary data construct the common complex-ratio
polydisk and prove its full coefficient obstruction. No admissible-family or
uniform-estimate existence is assumed. -/
theorem exists_negative_high_ratio_family_obstruction {b : ℝ} {z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (hprime : b∈primePhaseCosines)
    (he0 : edgeParameter (b:ℂ) (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z=>edgeParameter (b:ℂ) (z,lam₀*z)) z₀≠0) :
    ∃F : ComplexRatioFamily (edgeParameter (b:ℂ)) highPrefactor (-1) z₀ lam₀,
      CompactNegativeCoefficientObstruction F.coupling
        (NegativeRatioFamily.particleAmplitude F) (closedBall lam₀ F.radius) := by
  obtain ⟨F⟩ := negative_high_complex_ratio_family hK hp hS hB he0 hd
  exact ⟨F,negative_ratio_family_obstruction F hprime⟩

end
end IsingBulk.Joint.Negative
