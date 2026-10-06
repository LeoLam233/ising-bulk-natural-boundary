import IsingBulk.First.MeanSideIsolation
import IsingBulk.First.MeanJointAnalytic
import IsingBulk.First.MeanDerivativeTube

/-! Uniform actual s-derivative bounds on a compact mean annulus. It contains
both the three displaced sides and the real smooth-to-hard cutoff edge region. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Metric
open scoped Topology

def meanSeparatedAnnulus (delta : ℝ) : Set ℂ := {v | delta/2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2*delta}

theorem meanSeparatedAnnulus_compact (delta : ℝ) : IsCompact (meanSeparatedAnnulus delta) := by
  have hc : IsClosed (meanSeparatedAnnulus delta) :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  apply (isCompact_closedBall (0:ℂ) (2*delta)).of_isClosed_subset hc
  intro v hv
  simpa only [mem_closedBall,dist_zero_right] using hv.2

abbrev MeanSideParameters (n : ℕ) := ℂ × ℝ × (Fin n → ℝ)

def meanParameterPullback (n : ℕ) (q : MeanSideParameters n × ℂ) : ℂ × (Fin (n+1) → ℂ) :=
  (q.1.1,meanComplexCoordinates q.1.2.1 q.1.2.2 q.2)

theorem meanParameterPullback_continuous (n : ℕ) : Continuous (meanParameterPullback n) := by
  unfold meanParameterPullback
  apply Continuous.prodMk (by fun_prop)
  apply continuous_pi
  intro j
  have hs : Continuous (fun q : MeanSideParameters n × ℂ => shapeExtend q.1.2.2 j) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [shapeExtend_last]
      fun_prop
    · simp only [shapeExtend_castSucc]
      fun_prop
  unfold meanComplexCoordinates
  fun_prop

theorem meanParameterPullback_base_norm_le (a : OrderedChartData) (n : ℕ) (v : ℂ) :
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

/-- The actual source density is jointly analytic along the whole fixed
base annulus; no zero denominator or branch convention is assumed. -/
theorem actual_mean_separated_base_analytic (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ v ∈ meanSeparatedAnnulus delta,
      AnalyticAt ℂ (complexMeanFullDensity a.alpha)
        (meanParameterPullback n ((exp ((a.theta:ℂ)*I),0,0),v)) := by
  obtain ⟨rF,hrF,hF⟩ := complexMeanFullDensity_local_analytic a (n+1)
  obtain ⟨rZ,hrZ,hZ⟩ := centralMeanZ_linear_gap a n hbeta
  let delta := min (rF/4) (min (rZ/4) (Real.pi/4))
  have hd : 0 < delta := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdF : delta ≤ rF/4 := min_le_left _ _
  have hdZ : delta ≤ rZ/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdpi : delta ≤ Real.pi/4 := (min_le_right _ _).trans (min_le_right _ _)
  let p₀ : MeanSideParameters n := (exp ((a.theta:ℂ)*I),0,0)
  have hbase (v : ℂ) (hv : v ∈ meanSeparatedAnnulus delta) :
      AnalyticAt ℂ (complexMeanFullDensity a.alpha) (meanParameterPullback n (p₀,v)) := by
    have hvp : 0 < ‖v‖ := lt_of_lt_of_le (by positivity : 0 < delta/2) hv.1
    have hv0 : v ≠ 0 := norm_pos_iff.mp hvp
    have hvF : ‖v‖ < rF := by linarith [hv.2]
    have hvZ : ‖v‖ < rZ := by linarith [hv.2]
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
      linarith [hv.2,Real.pi_pos]
  exact ⟨delta,hd,hbase⟩

theorem actual_mean_separated_derivative_bounds (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ delta r : ℝ, 0 < delta ∧ 0 < r ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (s : ℂ) (rho : ℝ) (t : Fin n → ℝ),
        ‖(s,rho,t)-(exp ((a.theta:ℂ)*I),0,0)‖ ≤ r →
        ∀ v : ℂ, delta/2 ≤ ‖v‖ → ‖v‖ ≤ 2*delta →
          ‖(deriv^[j] (fun z => meanLocalDensity z rho a.alpha t v)) s‖ ≤ C := by
  obtain ⟨delta,hd,hbase⟩ := actual_mean_separated_base_analytic a n halpha hbeta
  let p₀ : MeanSideParameters n := (exp ((a.theta:ℂ)*I),0,0)
  obtain ⟨r,hr,hbound⟩ := compact_analytic_parameter_tube (meanSeparatedAnnulus_compact delta)
    (complexMeanFullDensity a.alpha) (meanParameterPullback n) (meanParameterPullback_continuous n) p₀ hbase
  refine ⟨delta,r,hd,hr,?_⟩
  intro j
  obtain ⟨C,hC,hb⟩ := hbound j
  refine ⟨C,hC,?_⟩
  intro s rho t hp v hvlo hvhi
  have hh := hb (s,rho,t) hp v ⟨hvlo,hvhi⟩
  change ‖meanParameterIter (complexMeanFullDensity a.alpha) j (s,meanComplexCoordinates rho t v)‖ ≤ C at hh
  rw [meanParameterIter_eq_iteratedDeriv] at hh
  have he : (fun z => complexMeanFullDensity a.alpha (z,meanComplexCoordinates rho t v)) =
      (fun z => meanLocalDensity z rho a.alpha t v) :=
    funext (fun z => complexMeanFullDensity_mean_coordinates z rho a.alpha t v)
  rwa [he] at hh

end
end IsingBulk.First
