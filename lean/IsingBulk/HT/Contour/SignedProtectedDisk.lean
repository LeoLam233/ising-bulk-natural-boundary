import IsingBulk.HT.Contour.SignedContinuation
import IsingBulk.HT.Contour.SignedProtectedGeometry

/-! Complete named-current holomorphy on the protected c*lambdaStar/N²
disk for either HT sign, with the actual constructed support. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set Metric
open scoped Topology BigOperators
set_option maxHeartbeats 1200000

theorem signed_constructed_current_holomorphic_disk (σ : ℂ) (hσ : ‖σ‖=1) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ : ℝ, 0 < c ∧ 0 < eps₀ ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
          AnalyticOnNhd ℂ (signedContinuedCurrentSlice σ N (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam)
            (closedBall (radialParameter d.theta eps) (c*lamStar/(N:ℝ)^2)) := by
  obtain ⟨ηA,τ₀,hηA,hτ₀,hroot⟩ := constructed_current_actual_root_disk d hcsmall
  let η₀ := min ηA (Real.sin d.thetaB/4)
  refine ⟨η₀,τ₀,lt_min hηA (by have := d.a_pos; positivity),hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  obtain ⟨cA,eps₀,a,hcA,heps₀,ha,hroots⟩ := hroot η α τ hη
    (hηlt.trans_le (min_le_left _ _)) hα hαsmall hτ hτlt
  let c := min (cA/4) (1/8:ℝ)
  have hc : 0<c := lt_min (by positivity) (by norm_num)
  refine ⟨c,eps₀,hc,heps₀,?_⟩
  intro N eps lamStar lam hN heps hepslt hls hl hl1
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let rad := c*lamStar/(N:ℝ)^2
  let U := ball (radialParameter d.theta eps) (2*rad)
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hrad : 0 < rad := by dsimp [rad]; positivity
  have hl0 : 0 < lam := hls.trans_le hl
  have hreg := constructedSelector_regular d.thetaB η α d.a_pos hη
    (hηlt.le.trans (min_le_right _ _)) hα
  have hsNonzero (s : ℂ) (hs : s ∈ U) : s ≠ 0 := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hdist : ‖s-radialParameter d.theta eps‖ < 2*rad := by simpa [U,dist_eq_norm] using hs
    have hn2 : 1 ≤ (N:ℝ)^2 := by nlinarith
    have hradc : rad ≤ c := (div_le_self (by positivity) hn2).trans
      (mul_le_of_le_one_right hc.le (hl.trans hl1))
    have hc1 : c ≤ 1/8 := min_le_right _ _
    have hncenter : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
    have hhalf := norm_ge_half_of_near_unit hncenter
      (show ‖s-radialParameter d.theta eps‖ < 1/2 by linarith)
    exact norm_pos_iff.mp (by linarith)
  have hsource (s : ℂ) (hs : s ∈ U) (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :=
    hroots N eps lamStar lam θ q s hN heps hepslt hls hl hl1 hθ.1 hθ.2 (by
      have hdist : ‖s-radialParameter d.theta eps‖ < 2*rad := by simpa [U,dist_eq_norm] using hs
      have hradA : rad ≤ (cA*lamStar/(N:ℝ)^2)/4 := by
        have hh := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left (cA/4) (1/8:ℝ)) hls.le) (sq_nonneg (N:ℝ))
        convert hh using 1; ring
      have hx : 0 < cA*lamStar/(N:ℝ)^2 := by positivity
      linarith)
  have hY (θ : Fin N → ℝ) : 1-σ*coordinateProduct (deformedPoint f r τ lam θ) ≠ 0 :=
    signed_gap_ne_zero σ _ hσ (homotopy_y_product_lt_one (by omega) f (Real.exp_pos _)
      (Real.exp_lt_one_iff.mpr (by have := d.c₀_pos; nlinarith)) hτ.le hl0.le θ
      hreg.p_nonneg hreg.m_le_one)
  have hZ (s : ℂ) (hs : s ∈ U) (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0 := by
    have hz := (hsource s hs q θ hθ).2.2.1.trans_lt
      (Real.exp_lt_one_iff.mpr (show -a*lam < 0 by nlinarith))
    exact signed_gap_ne_zero σ _ hσ hz
  have hnamed (q : Fin N) : AnalyticOnNhd ℂ
      (signedContinuedNamedCurrentIntegral σ N f r τ lam q) U :=
    signed_continuedNamedCurrentIntegral_analyticOn_of_gaps σ N f (Real.exp_pos _).ne' τ lam q
      hreg.p_smooth hreg.m_smooth hreg.a_smooth isOpen_ball hsNonzero
      (fun s hs θ hθ => (hsource s hs q θ hθ).2.1) (fun θ _ => hY θ)
      (fun s hs θ hθ => hZ s hs q θ hθ)
  intro s hs
  have hsU : s ∈ U := by
    have hdist : dist s (radialParameter d.theta eps) ≤ rad := hs
    change dist s (radialParameter d.theta eps) < 2*rad
    linarith
  exact Finset.analyticAt_fun_sum _ (fun q _ => hnamed q s hsU)

end
end IsingBulk.HT.Contour
