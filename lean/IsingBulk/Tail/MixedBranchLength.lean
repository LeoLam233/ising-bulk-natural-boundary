import IsingBulk.Tail.MixedBranchCone
import IsingBulk.Analysis.BranchLength

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped Topology

/-- A single integrable majorant works for every admissible coupled
occupancy. It retains the actual current branch and includes lambda zero. -/
theorem mixed_plateau_slope_majorant (d : LocalBranchData) :
    ∃ B R τ₀ : ℝ,0<B ∧ 0<R ∧ 0<τ₀ ∧ ∀ eps τ t u : ℝ,
      0<eps → eps≤R → 0≤τ → τ<τ₀ → 0≤t → t≤1 → |u|≤R →
      ‖mixedSourceSlope (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u)‖≤
        B/Real.sqrt (|u|+eps) := by
  obtain ⟨_c,B,rM,_hc,hB,hrM,hMagnitude⟩ := current_derivative_magnitude d
  obtain ⟨rI,hrI,hInclusion⟩ := current_branch_inclusion d
  let R := min rM rI/2
  have hR : 0<R := by dsimp [R]; positivity
  have hRM : R<rM := by dsimp [R]; linarith [min_le_left rM rI,lt_min hrM hrI]
  have hRI : R<rI := by dsimp [R]; linarith [min_le_right rM rI,lt_min hrM hrI]
  refine ⟨B,R,d.tau*R,hB,hR,mul_pos d.tau_pos hR,?_⟩
  intro eps τ t u he heR hτ hτR ht ht1 huR
  have ht0 : 0≤(τ/d.tau)*t := mul_nonneg (div_nonneg hτ d.tau_pos.le) ht
  have htR : (τ/d.tau)*t<R := by
    have hh : τ/d.tau<R := (div_lt_iff₀ d.tau_pos).mpr (by simpa [mul_comm] using hτR)
    exact (mul_le_of_le_one_right (div_nonneg hτ d.tau_pos.le) ht1).trans_lt hh
  obtain ⟨hRe,hIm⟩ := hInclusion eps ((τ/d.tau)*t) u he (heR.trans_lt hRI) ht0 (htR.trans hRI) (huR.trans_lt hRI)
  rw [← plateauY_rescale_tau d eps τ t u,mixedSourceSlope_current_deriv d eps ((τ/d.tau)*t) u hRe hIm]
  have hh := (hMagnitude eps ((τ/d.tau)*t) u he (heR.trans_lt hRM) ht0 (htR.trans hRM) (huR.trans_lt hRM)).2
  exact hh.trans (div_le_div_of_nonneg_left hB.le (by positivity)
    (Real.sqrt_le_sqrt (by linarith)))

theorem mixed_actual_branch_slope_majorant (d : LocalBranchData) :
    ∃ B R τ₀ : ℝ,0<B ∧ 0<R ∧ 0<τ₀ ∧
      ∀ (N : ℕ) (eps τ lam : ℝ) (f : SelectorFunctions) (θ : Fin N → ℝ) (j : Fin N),
      0<N → 0<eps → eps≤R → 0≤τ → τ<τ₀ → 0≤lam → lam≤1 →
      (∀ x,0≤f.p x ∧ f.p x≤1) → f.p (θ j)=0 → f.m (θ j)=1 →
      |θ j+d.thetaB-2*Real.pi|≤R →
      ‖mixedSourceSlope (radialParameter d.theta eps)
        (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ j)‖≤
        B/Real.sqrt (|θ j+d.thetaB-2*Real.pi|+eps) := by
  obtain ⟨B,R,τ₀,hB,hR,hτ₀,hBound⟩ := mixed_plateau_slope_majorant d
  refine ⟨B,R,τ₀,hB,hR,hτ₀,?_⟩
  intro N eps τ lam f θ j hN he heR hτ hτlt hl0 hl1 hp hpj hmj huR
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun i => (hp (θ i)).1)
  have hPN := occupancy_le (fun i => (hp (θ i)).2)
  rw [deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ j hpj hmj]
  apply hBound eps τ _ _ he heR hτ hτlt (by positivity) _ huR
  exact (div_le_one hn).mpr ((mul_le_of_le_one_left hP0 hl1).trans hPN)

/-- Spectator majorants have a uniform L1 cost independent of epsilon. -/
theorem mixed_branch_majorant_integral {eps R B : ℝ} (he : 0<eps) (hR : 0≤R) (hB : 0≤B) :
    IntegrableOn (fun u : ℝ => B/Real.sqrt (|u|+eps)) (Icc (-R) R) ∧
    (∫ u in Icc (-R) R, B/Real.sqrt (|u|+eps))≤4*B*Real.sqrt R := by
  have hc : Continuous (fun u : ℝ => B/Real.sqrt (|u|+eps)) :=
    continuous_const.div (continuous_abs.add continuous_const).sqrt
      (fun u => (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg u) he)).ne')
  refine ⟨hc.continuousOn.integrableOn_compact isCompact_Icc,?_⟩
  have hh := reciprocal_sqrt_integral eps R B he hR hB
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc] at hh
  exact hh

end
end IsingBulk.Tail
