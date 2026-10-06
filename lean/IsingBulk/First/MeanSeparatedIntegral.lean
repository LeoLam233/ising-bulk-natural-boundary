import IsingBulk.First.MeanAnalyticIntegral
import IsingBulk.First.MeanSmallAnnulus

/-! Actual differentiated side/edge integrals. All analytic and denominator
conditions are derived from the physical source, with fixed real weights. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory Metric Complex
open scoped Topology

theorem meanSideParameter_norm_le (s s₀ : ℂ) (rho r : ℝ) {n : ℕ} (t : Fin n → ℝ)
    (hs : ‖s-s₀‖ ≤ r) (ht : ‖(rho,t)‖ ≤ r) : ‖(s,rho,t)-(s₀,0,0)‖ ≤ r := by
  simpa only [Prod.mk_sub_mk,sub_zero,Prod.norm_def] using max_le hs ht

theorem meanComplexCoordinates_continuous_curve {n : ℕ} (rho : ℝ) (t : Fin n → ℝ)
    {v : ℝ → ℂ} (hv : Continuous v) : Continuous (fun x => meanComplexCoordinates rho t (v x)) := by
  apply continuous_pi
  intro j
  unfold meanComplexCoordinates
  fun_prop

theorem meanParameterIter_actual_density {n : ℕ} (alpha rho : ℝ) (t : Fin n → ℝ)
    (v s : ℂ) (j : ℕ) :
    meanParameterIter (complexMeanFullDensity alpha) j (s,meanComplexCoordinates rho t v) =
      (deriv^[j] (fun z => meanLocalDensity z rho alpha t v)) s := by
  rw [meanParameterIter_eq_iteratedDeriv]
  have he : (fun z => complexMeanFullDensity alpha (z,meanComplexCoordinates rho t v)) =
      (fun z => meanLocalDensity z rho alpha t v) :=
    funext (fun z => complexMeanFullDensity_mean_coordinates z rho alpha t v)
  rw [he]

/-- A selectable sufficiently small annulus gives actual interchange and
uniform bounds for any fixed compact side/edge parametrization and fixed weight.
The radius and shape tube are chosen before every derivative order. -/
theorem actual_mean_separated_integrals (a : OrderedChartData) (n : ℕ)
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
end IsingBulk.First
