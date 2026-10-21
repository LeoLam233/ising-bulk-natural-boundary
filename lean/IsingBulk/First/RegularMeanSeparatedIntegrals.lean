import IsingBulk.First.RegularMeanCentralPole
import IsingBulk.First.RegularMeanJointAnalytic
import IsingBulk.First.MeanSeparatedIntegral

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

open MeasureTheory Metric

theorem meanParameterPullback_base_norm_le (a : RegularChartData) (n : ℕ) (v : ℂ) :
    ‖meanParameterPullback n ((exp ((a.theta:ℂ)*I),0,0),v)-
      (exp ((a.theta:ℂ)*I),(0 : Fin (n+1) → ℂ))‖ ≤ ‖v‖ := by
  have hN : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnormN : ‖(n+1:ℂ)‖ = (n+1:ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Complex.norm_natCast (n+1)
  simp only [meanParameterPullback, Prod.mk_sub_mk, sub_self, sub_zero,
    Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro j
  simp only [meanComplexCoordinates,shapeExtend_zero,Pi.zero_apply,Complex.ofReal_zero,zero_add,mul_zero,sub_zero]
  rw [norm_div,hnormN]
  exact div_le_self (norm_nonneg v) hN

theorem actual_mean_punctured_base_analytic (a : RegularChartData) (n : ℕ)
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
theorem actual_mean_small_annulus_tube (a : RegularChartData) (n : ℕ)
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
/-- A selectable sufficiently small annulus gives actual interchange and
uniform bounds for any fixed compact side/edge parametrization and fixed weight.
The radius and shape tube are chosen before every derivative order. -/
theorem actual_mean_separated_integrals (a : RegularChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ (K : Set ℝ), IsCompact K →
        ∀ (v : ℝ → ℂ), Continuous v → MapsTo v K (meanSeparatedAnnulus delta) →
        ∀ (w : ℝ → ℂ), ContinuousOn w K →
        (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ s : ℂ,
          ‖s-exp ((a.theta:ℂ)*I)‖ < r →
          AnalyticAt ℂ (fun z => ∫ x in K, w x * meanLocalDensity z rho a.alpha t (v x)) s) ∧
        (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ (j : ℕ) (s : ℂ),
          ‖s-exp ((a.theta:ℂ)*I)‖ < r →
          (deriv^[j] (fun z => ∫ x in K, w x * meanLocalDensity z rho a.alpha t (v x))) s =
            ∫ x in K, w x * (deriv^[j] (fun z => meanLocalDensity z rho a.alpha t (v x))) s) ∧
        (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r →
          ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < r →
          ‖(deriv^[j] (fun z => ∫ x in K, w x * meanLocalDensity z rho a.alpha t (v x))) s‖ ≤ C) := by
  obtain ⟨D,hD,hTube⟩ := actual_mean_small_annulus_tube a n halpha hbeta
  refine ⟨D,hD,?_⟩
  intro delta hd hdD
  obtain ⟨r,hr,hA,hB⟩ := hTube delta hd hdD
  refine ⟨r,hr,?_⟩
  intro K hK v hv hvK w hw
  let s₀ := exp ((a.theta:ℂ)*I)
  have hEq (rho : ℝ) (t : Fin n → ℝ) (ht : ‖(rho,t)‖ ≤ r) (j : ℕ) (s : ℂ)
      (hs : ‖s-s₀‖ < r) :
      AnalyticAt ℂ (fun z => ∫ x in K, w x * meanLocalDensity z rho a.alpha t (v x)) s ∧
      (deriv^[j] (fun z => ∫ x in K, w x * meanLocalDensity z rho a.alpha t (v x))) s =
        ∫ x in K, w x * (deriv^[j] (fun z => meanLocalDensity z rho a.alpha t (v x))) s := by
    have ha' (z : ℂ) (hz : z ∈ ball s₀ r) (x : ℝ) (hx : x ∈ K) :
        AnalyticAt ℂ (complexMeanFullDensity a.alpha) (z,meanComplexCoordinates rho t (v x)) := by
      apply hA (z,rho,t) (meanSideParameter_norm_le z s₀ rho r t ?_ ht) (v x) (hvK hx)
      exact le_of_lt (by simpa [mem_ball,dist_eq_norm] using hz)
    have hb' (i : ℕ) : ∃ C : ℝ, ∀ z ∈ ball s₀ r, ∀ x ∈ K,
        ‖meanParameterIter (complexMeanFullDensity a.alpha) i (z,meanComplexCoordinates rho t (v x))‖ ≤ C := by
      obtain ⟨C,_hC,hb⟩ := hB i
      refine ⟨C,?_⟩
      intro z hz x hx
      exact hb (z,rho,t) (meanSideParameter_norm_le z s₀ rho r t
        (le_of_lt (by simpa [mem_ball,dist_eq_norm] using hz)) ht) (v x) (hvK hx)
    have he := analytic_weighted_compact_integral_iteratedDeriv hK isOpen_ball
      (complexMeanFullDensity a.alpha) (fun x => meanComplexCoordinates rho t (v x))
      (meanComplexCoordinates_continuous_curve rho t hv) w hw ha' hb' j s
      (by simpa [mem_ball,dist_eq_norm] using hs)
    simp only [complexMeanFullDensity_mean_coordinates,meanParameterIter_actual_density] at he
    have han := analytic_weighted_compact_integral_analyticAt hK isOpen_ball
      (complexMeanFullDensity a.alpha) (fun x => meanComplexCoordinates rho t (v x))
      (meanComplexCoordinates_continuous_curve rho t hv) w hw ha' hb' s
      (by simpa [mem_ball,dist_eq_norm] using hs)
    simp only [complexMeanFullDensity_mean_coordinates] at han
    exact ⟨han,he⟩
  refine ⟨fun rho t ht s hs => (hEq rho t ht 0 s hs).1,
    fun rho t ht j s hs => (hEq rho t ht j s hs).2,?_⟩
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hw
  intro j
  obtain ⟨C,hC,hb⟩ := hB j
  let B := max M 0*C*volume.real K
  refine ⟨B+1,by dsimp [B]; positivity,?_⟩
  intro rho t ht s hs
  rw [(hEq rho t ht j s hs).2]
  apply (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top ?_).trans
    (show B ≤ B+1 by linarith)
  intro x hx
  rw [norm_mul]
  have hpoint := hb (s,rho,t) (meanSideParameter_norm_le s s₀ rho r t hs.le ht) (v x) (hvK hx)
  change ‖meanParameterIter (complexMeanFullDensity a.alpha) j (s,meanComplexCoordinates rho t (v x))‖ ≤ C at hpoint
  rw [meanParameterIter_actual_density] at hpoint
  exact mul_le_mul ((hM x hx).trans (le_max_left _ _)) hpoint (norm_nonneg _) (le_max_right _ _)

end
end IsingBulk.First.Regular
