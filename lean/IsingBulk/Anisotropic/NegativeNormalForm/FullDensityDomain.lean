import IsingBulk.Anisotropic.NegativeNormalForm.CoincidenceUniformBounds
import IsingBulk.Anisotropic.NegativeNormalForm.FullTransformedDensity

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter IsingBulk.First
open scoped Topology BigOperators

theorem actualPairMultiplier_analyticOnNhd {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v)) :
    AnalyticOnNhd ℂ (actualPairMultiplier Phi) (ball 0 r) := by
  intro v hv
  apply Finset.analyticAt_fun_prod
  intro p hp
  exact coincidenceFactor_analyticOnNhd Phi r hPhi heq p.1 p.2
    (ne_of_lt (mem_firstStrictPairs p |>.mp hp)) v hv

theorem actual_vandermonde_pullback_on_ball {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (v : Config n) (hv : ‖v‖<r) :
    vandermonde (Phi v)^2=vandermonde v^2*actualPairMultiplier Phi v^2 := by
  apply vandermonde_sq_dividedDifference
  intro i j hij
  exact coincidenceFactor_identity_on_ball Phi r hPhi heq i j (ne_of_lt hij) v hv

/-- Full literal residue pullback on the entire common configuration ball,
including every Vandermonde collision divisor. No chart-dimension radius loss. -/
theorem poleResidue_full_pullback_on_ball {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (u : Config m) (hu : ‖freeChartCLM m u‖<r) :
    poleResidue B rootB phi hphi d T (Phi (freeChartCLM m u))*constrainedJacobian Phi u=
      vandermonde (freeChartCLM m u)^2*fullTransformedDensity B rootB phi hphi d T Phi u := by
  rw [poleResidue_factor,actual_vandermonde_pullback_on_ball Phi r hPhi heq _ hu]
  unfold fullTransformedDensity
  ring

theorem actualPairMultiplier_ne_zero_on_ball {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (c : NNReal) (hc : (c:ℝ)<1)
    (hLip : LipschitzOnWith c (fun v => Phi v-v) (closedBall 0 r))
    (v : Config n) (hv : ‖v‖<r) : actualPairMultiplier Phi v≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp hz
  change coincidenceFactor Phi p.1 p.2 v=0 at hz
  have h := coincidenceFactor_uniform_close Phi r hPhi heq c hLip p.1 p.2
    (ne_of_lt (mem_firstStrictPairs p |>.mp hp)) v hv
  rw [hz,zero_sub,norm_neg,norm_one] at h
  exact (not_le_of_gt hc) h

end
end IsingBulk.Anisotropic.NegativeNormalForm
