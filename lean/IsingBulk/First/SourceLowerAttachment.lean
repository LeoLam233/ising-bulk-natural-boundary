import IsingBulk.First.SourceAsymptoticAttachment

/-! Transfer of the genuine common-support lower-derivative bounds to the
actual weighted reduced form factor. The same positive source approach interval
is retained before every lower derivative order. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter IsingBulk.Branch
open scoped Topology

theorem CompatibleYCutoffData.attach_local_lower_bounds {n : ℕ} {alpha beta : ℝ}
    {U : Set (Fin n → ℝ)} (c : CompatibleYCutoffData n alpha beta U)
    (a : OrderedChartData) (k : ℕ) (e : ℝ) (he : 0 < e)
    (hlocal : ∀ j : ℕ, j < k → ∃ C : ℝ, 0 < C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < e →
        ‖(deriv^[j] (localizedSmoothMeanIntegral a (liftShapeCutoff c.chi)
          (fun v => (c.eta v:ℂ)) (-(Real.sin a.theta/4)*epsilon) c.delta))
            (radialParameter a.theta epsilon)‖ ≤ C) :
    ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j < k → ∃ C : ℝ, 0 < C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < e →
        ‖radialWeightedDerivative n j a.theta (fixedYChartWeight a.alpha c.chi c.eta) epsilon‖ ≤ C := by
  obtain ⟨eM,heM,_,hmargin⟩ := radial_disk_source_trace_margin a.sin_theta_pos
  refine ⟨min e eM,lt_min he heM,?_⟩
  intro j hj
  obtain ⟨C,hC,hb⟩ := hlocal j hj
  refine ⟨C,hC,?_⟩
  intro epsilon he heR
  have heL' : epsilon < e := heR.trans_le (min_le_left _ _)
  have heM' : epsilon < eM := heR.trans_le (min_le_right _ _)
  have hr1 : Real.exp (-(Real.sin a.theta/4)*epsilon) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos a.sin_theta_pos he]
  have hm := (hmargin epsilon he heM' (radialParameter a.theta epsilon)
    (by simpa using mul_pos (div_pos a.sin_theta_pos (by norm_num) : 0 < Real.sin a.theta/16) he)).2
  rw [radialWeightedDerivative,c.source_localizedSmoothMean_derivative a _ _ hr1 hm j]
  exact hb epsilon he heL'

end
end IsingBulk.First
