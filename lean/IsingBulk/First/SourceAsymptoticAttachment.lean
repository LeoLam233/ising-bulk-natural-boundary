import IsingBulk.First.CompatibleMeanAttachment
import IsingBulk.First.RadialFirstRepresentation

/-! Transfer of an already proved actual local mean asymptotic to the literal
weighted reduced form factor, via neighborhood equality at a fixed radius. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter IsingBulk.Branch
open scoped Topology

def radialWeightedDerivative (n j : ℕ) (theta : ℝ) (w : (Fin (n+1) → ℝ) → ℝ)
    (epsilon : ℝ) : ℂ :=
  iteratedDeriv j (fun s => weightedReducedFormFactor (n+1)
    (Real.exp (-(Real.sin theta/4)*epsilon)) (globalRoot s) w)
    (radialParameter theta epsilon)

theorem CompatibleYCutoffData.attach_local_asymptotic {n : ℕ} {alpha beta : ℝ}
    {U : Set (Fin n → ℝ)} (c : CompatibleYCutoffData n alpha beta U)
    (a : OrderedChartData) (j : ℕ) (L : ℂ)
    (hlocal : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[j] (localizedSmoothMeanIntegral a (liftShapeCutoff c.chi)
        (fun v => (c.eta v:ℂ)) (-(Real.sin a.theta/4)*epsilon) c.delta))
          (radialParameter a.theta epsilon) - (Real.sqrt epsilon:ℂ)⁻¹*L)
      (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹)) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => radialWeightedDerivative n j a.theta
        (fixedYChartWeight a.alpha c.chi c.eta) epsilon - (Real.sqrt epsilon:ℂ)⁻¹*L)
      (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) := by
  obtain ⟨e,he,_,hmargin⟩ := radial_disk_source_trace_margin a.sin_theta_pos
  apply hlocal.congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with epsilon hp hsmall
  have hr1 : Real.exp (-(Real.sin a.theta/4)*epsilon) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos a.sin_theta_pos hp]
  have hm := (hmargin epsilon hp hsmall (radialParameter a.theta epsilon)
    (by simpa using mul_pos (show 0 < Real.sin a.theta/16 from div_pos a.sin_theta_pos (by norm_num)) hp)).2
  rw [radialWeightedDerivative,c.source_localizedSmoothMean_derivative a _ _ hr1 hm j]

end
end IsingBulk.First
