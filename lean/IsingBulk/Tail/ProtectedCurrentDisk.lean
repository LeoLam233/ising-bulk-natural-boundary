import IsingBulk.Tail.ProtectedAngularWrap
import IsingBulk.Tail.CurrentDerivatives

/-! A common protected disk for the actual fixed-lambda angular current.
Only geometric cutoff-support conditions are inputs; holomorphy and root
products are constructed. The angular integration box is handled literally. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory Metric
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 800000

def ProtectedCurrentSupports (d : LocalBranchData) (N : ℕ) (f : SelectorFunctions)
    (h R σ : ℝ) : Prop :=
  ∀ (q : Fin N) (θ : Fin N → ℝ), θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q) →
    f.p (signedAngles θ q)=1 ∧ f.m (signedAngles θ q)=0 ∧
    σ ≤ Real.sin (signedAngles θ q) ∧ h ≤ |(|signedAngles θ q|-d.thetaB)| ∧
    ∀ i, h ≤ |(|signedAngles θ i|-d.thetaB)| ∨
      (f.p (signedAngles θ i)=0 ∧ f.m (signedAngles θ i)=1 ∧ |signedAngles θ i+d.thetaB| < R)

/-- The source's closed c lambda*/N² disk is a conclusion. The geometric
support predicate is about actual periodic bump values and angular positions,
not a substituted analytic or norm-bound hypothesis. -/
theorem protected_current_closed_disk (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {σ : ℝ} (hσ : 0 < σ) :
    ∃ h R r : ℝ, 0 < h ∧ h < R ∧ h < d.thetaB ∧ d.thetaB+h < Real.pi ∧ 0 < r ∧
      ∀ τ : ℝ, 0 < τ → τ < r → ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) (f : SelectorFunctions) (eps lamStar lam : ℝ),
        1 ≤ N → 0 < eps → eps < r → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
        ContDiff ℝ ∞ f.p → ContDiff ℝ ∞ f.m → ContDiff ℝ ∞ f.a →
        Function.Periodic f.p (2*Real.pi) → Function.Periodic f.m (2*Real.pi) →
        (∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) → (∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1) →
        (∀ x, Real.sin x ≤ 0 → f.p x=0) → (∀ x, 0 ≤ Real.sin x → f.m x=0) →
        ProtectedCurrentSupports d N f h R σ →
        AnalyticOnNhd ℂ (continuedCurrentSlice N f (Real.exp (-d.c₀*eps)) τ lam)
          (closedBall (radialParameter d.theta eps) (c*lamStar/(N:ℝ)^2)) := by
  obtain ⟨h,R,r,hh,hhR,hhb,hhπ,hr,hroot⟩ := protected_deformed_root_product d hcsmall hσ
  refine ⟨h,R,r,hh,hhR,hhb,hhπ,hr,?_⟩
  intro τ hτ hτr
  obtain ⟨c₀,cq,hc₀,hcq,hroots⟩ := hroot τ hτ hτr
  let c := min (c₀/4) (1/8:ℝ)
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc : c ≤ c₀/4 := min_le_left _ _
  have hc1 : c ≤ 1/8 := min_le_right _ _
  refine ⟨c,hc,?_⟩
  intro N f eps lamStar lam hN heps hepsr hls hl hl1 hp hm ha hpper hmper hpv hmv hps hms hsupp
  have hN0 : 0 < N := by omega
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hn2 : 1 ≤ (N:ℝ)^2 := by nlinarith
  have hl0 : 0 < lam := hls.trans_le hl
  let rad := c*lamStar/(N:ℝ)^2
  have hrad : 0 < rad := by dsimp [rad]; positivity
  have hradc : rad ≤ c := by
    have h₁ : c*lamStar/(N:ℝ)^2 ≤ c*lamStar := div_le_self (by positivity) hn2
    exact h₁.trans (mul_le_of_le_one_right hc.le (hl.trans hl1))
  let U := ball (radialParameter d.theta eps) (2*rad)
  have hU : IsOpen U := isOpen_ball
  have hsNonzero (s : ℂ) (hs : s ∈ U) : s ≠ 0 := by
    have hncenter : 1 ≤ ‖radialParameter d.theta eps‖ := by
      rw [radialParameter_norm heps.le]; linarith
    have hdist : ‖s-radialParameter d.theta eps‖ < 2*rad := by simpa [U,dist_eq_norm] using hs
    have hhalf := norm_ge_half_of_near_unit hncenter (show ‖s-radialParameter d.theta eps‖ < 1/2 by linarith)
    exact norm_pos_iff.mp (by linarith)
  have hsource (s : ℂ) (hs : s ∈ U) (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      (∀ i, sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i) ∈ continuedRootDomain) ∧
      ‖∏ i, continuedRoot (sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ≤
        Real.exp (-(cq/2)*lam) := by
    obtain ⟨hpq,hmq,hσq,hqsep,htypes⟩ := hsupp q θ hθ
    have hdist : ‖s-radialParameter d.theta eps‖ < 2*rad := by simpa [U,dist_eq_norm] using hs
    have hdisc : ‖s-radialParameter d.theta eps‖ ≤ c₀*lamStar/(N:ℝ)^2 := by
      have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hls.le) (sq_nonneg (N:ℝ))
      dsimp [rad] at hdist
      have he : c₀/4*lamStar/(N:ℝ)^2=(c₀*lamStar/(N:ℝ)^2)/4 := by ring
      rw [he] at hb
      have hx : 0 ≤ c₀*lamStar/(N:ℝ)^2 := by positivity
      linarith
    have hresult := hroots N f eps lamStar lam (signedAngles θ) q s hN heps hepsr hls hl hl1
      hpv hmv hps hms (signedAngles_mem_signed_box hθ.1) hpq hmq hσq hqsep htypes hdisc
    simpa only [deformedPoint_signedAngles f hpper hmper] using hresult
  have hY (θ : Fin N → ℝ) : 1-coordinateProduct (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ) ≠ 0 :=
    homotopy_y_gap_nonzero hN0 f (Real.exp_pos _)
      (Real.exp_lt_one_iff.mpr (by have := d.c₀_pos; nlinarith)) hτ.le hl0.le θ
      (fun x => (hpv x).1) (fun x => (hmv x).2)
  have hZ (s : ℂ) (hs : s ∈ U) (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      1-coordinateProduct (fun i => selectedContinuedRoot s
        (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)) ≠ 0 := by
    have hz := (hsource s hs q θ hθ).2.trans_lt
      (Real.exp_lt_one_iff.mpr (show -(cq/2)*lam < 0 by nlinarith))
    intro he
    have he' := (sub_eq_zero.mp he).symm
    change (∏ i, continuedRoot (sourceW s
      (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)))=1 at he'
    rw [he',norm_one] at hz
    exact lt_irrefl _ hz
  have hnamed (q : Fin N) : AnalyticOnNhd ℂ
      (continuedNamedCurrentIntegral N f (Real.exp (-d.c₀*eps)) τ lam q) U :=
    continuedNamedCurrentIntegral_analyticOn_of_gaps N f (Real.exp_pos _).ne' τ lam q hp hm ha hU hsNonzero
      (fun s hs θ hθ => (hsource s hs q θ hθ).1) (fun θ _ => hY θ)
      (fun s hs θ hθ => hZ s hs q θ hθ)
  intro s hs
  have hsU : s ∈ U := by
    have hdist : dist s (radialParameter d.theta eps) ≤ rad := hs
    change dist s (radialParameter d.theta eps) < 2*rad
    linarith
  exact Finset.analyticAt_fun_sum _ (fun q _ => hnamed q s hsU)

theorem continuedCurrentSlice_eventually_actual (N : ℕ) (hN : 0 < N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    continuedCurrentSlice N f r τ lam =ᶠ[𝓝 s] actualCurrentSlice N f r τ lam := by
  have hsD := dampingDomain_of_margin hr hr1 hmargin
  filter_upwards [dampingDomain_mem_nhds hsD] with z hz
  apply Finset.sum_congr rfl
  intro q _
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  unfold continuedNamedCurrentDensity namedCurrentDensity
  rw [continuedPulledDensity_eq_original f r τ lam z θ]
  intro i
  exact (sourceW_upper_of_margin hr hr1 hz.2 (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
    (deformed_sourceW_im_ge hN f hr hτ hlam θ z hp0 hm0 hps hms i)

end
end IsingBulk.Tail
