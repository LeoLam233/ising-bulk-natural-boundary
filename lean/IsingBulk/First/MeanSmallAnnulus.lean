import IsingBulk.First.MeanAnalyticTube

/-! Arbitrarily small compatible separated mean annuli. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Metric
open scoped Topology

theorem actual_mean_punctured_base_analytic (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : ℂ, 0 < ‖v‖ → ‖v‖ < R →
      AnalyticAt ℂ (complexMeanFullDensity a.alpha)
        (meanParameterPullback n ((exp ((a.theta:ℂ)*I),0,0),v)) := by
  obtain ⟨rF,hrF,hF⟩ := complexMeanFullDensity_local_analytic a (n+1)
  obtain ⟨rZ,hrZ,hZ⟩ := centralMeanZ_linear_gap a n hbeta
  let R := min (rF/2) (min (rZ/2) Real.pi)
  have hR : 0 < R := lt_min (by positivity) (lt_min (by positivity) Real.pi_pos)
  have hRF : R ≤ rF/2 := min_le_left _ _
  have hRZ : R ≤ rZ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRpi : R ≤ Real.pi := (min_le_right _ _).trans (min_le_right _ _)
  let p₀ : MeanSideParameters n := (exp ((a.theta:ℂ)*I),0,0)
  have hbase (v : ℂ) (hvp : 0 < ‖v‖) (hvR : ‖v‖ < R) :
      AnalyticAt ℂ (complexMeanFullDensity a.alpha) (meanParameterPullback n (p₀,v)) := by
    have hv0 : v ≠ 0 := norm_pos_iff.mp hvp
    have hvF : ‖v‖ < rF := by linarith
    have hvZ : ‖v‖ < rZ := by linarith
    have hzEq : complexDensityDenominator a.alpha (meanParameterPullback n (p₀,v)) =
        1-centralMeanZ a n v := by
      unfold complexDensityDenominator meanParameterPullback p₀
      rw [complexDensityZ_mean_coordinates]
      rfl
    have hyEq : complexMeanYDenominator a.alpha (meanParameterPullback n (p₀,v)) =
        centeredMeanDenominator v := by
      unfold complexMeanYDenominator meanParameterPullback p₀
      rw [complexDensityY_mean_coordinates,coordinateProduct_meanChartY]
      have hy := meanProductY_translate_pole (n+1) 0 a.alpha v (by simpa using halpha)
      simpa [physicalMeanPole,centeredMeanDenominator] using congrArg (fun z : ℂ => 1-z) hy
    apply hF _ ((meanParameterPullback_base_norm_le a n v).trans_lt hvF)
    · rw [hzEq]
      have hgap := hZ v hvZ
      exact norm_pos_iff.mp ((mul_pos (div_pos a.b_pos (by norm_num)) hvp).trans_le hgap)
    · rw [hyEq]
      apply centeredMeanDenominator_ne_zero hv0
      have habs := Complex.abs_re_le_norm v
      linarith [Real.pi_pos]
  exact ⟨R,hR,hbase⟩

/-- The mean radius may be chosen below any prior geometric threshold. One
parameter/shape tube then works for all derivative orders and all sides. -/
theorem actual_mean_small_annulus_tube (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧
      (∀ p : MeanSideParameters n, ‖p-(exp ((a.theta:ℂ)*I),0,0)‖ ≤ r →
        ∀ v ∈ meanSeparatedAnnulus delta, AnalyticAt ℂ (complexMeanFullDensity a.alpha)
          (meanParameterPullback n (p,v))) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ p : MeanSideParameters n, ‖p-(exp ((a.theta:ℂ)*I),0,0)‖ ≤ r →
        ∀ v ∈ meanSeparatedAnnulus delta,
          ‖meanParameterIter (complexMeanFullDensity a.alpha) j (meanParameterPullback n (p,v))‖ ≤ C) := by
  obtain ⟨R,hR,hbase⟩ := actual_mean_punctured_base_analytic a n halpha hbeta
  refine ⟨R/4,by positivity,?_⟩
  intro delta hd hdR
  have ha (v : ℂ) (hv : v ∈ meanSeparatedAnnulus delta) :=
    hbase v (lt_of_lt_of_le (by positivity : 0 < delta/2) hv.1)
      (by linarith [hv.2] : ‖v‖ < R)
  obtain ⟨rA,hrA,hA⟩ := compact_analytic_parameter_domain (meanSeparatedAnnulus_compact delta)
    (complexMeanFullDensity a.alpha) (meanParameterPullback n) (meanParameterPullback_continuous n)
    (exp ((a.theta:ℂ)*I),0,0) ha
  obtain ⟨rB,hrB,hB⟩ := compact_analytic_parameter_tube (meanSeparatedAnnulus_compact delta)
    (complexMeanFullDensity a.alpha) (meanParameterPullback n) (meanParameterPullback_continuous n)
    (exp ((a.theta:ℂ)*I),0,0) ha
  refine ⟨min rA rB,lt_min hrA hrB,?_,?_⟩
  · intro p hp v hv
    exact hA p (hp.trans (min_le_left _ _)) v hv
  · intro j
    obtain ⟨C,hC,hb⟩ := hB j
    exact ⟨C,hC,fun p hp v hv => hb p (hp.trans (min_le_right _ _)) v hv⟩

end
end IsingBulk.First
