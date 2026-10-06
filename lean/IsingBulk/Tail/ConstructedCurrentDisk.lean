import IsingBulk.Tail.ConstructedCurrentSupport
import IsingBulk.Tail.CurrentCompactContinuation
import IsingBulk.Tail.SelectedFDiskSupport
import IsingBulk.Tail.ProtectedSourceRoots
import IsingBulk.Tail.ProtectedDensity

/-! Actual protected root disk on the closed named-current support of the
same constructedSelector used by selected F. Angular widths precede tau;
all remaining constants precede N, epsilon, lambda and occupancy. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem deformedPoint_scale_lambda {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ lam θ i=deformedPoint f r (lam*τ) 1 θ i := by
  unfold deformedPoint retractionShift
  congr 2
  push_cast
  ring

theorem deformedPoint_current_plateau {N : ℕ} (f : SelectorFunctions) (b c₀ eps τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) (hp : f.p (θ i)=0) (hm : f.m (θ i)=1) :
    deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i =
      plateauY c₀ eps τ (lam*occupancy (fun j => f.p (θ j))/(N:ℝ)) b (θ i+b-2*Real.pi) := by
  rw [deformedPoint_scale_lambda,deformedPoint_selected_plateau f b c₀ eps (lam*τ) θ i hp hm]
  unfold plateauY
  congr 1
  push_cast
  ring

theorem constructed_current_actual_root_disk (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ a : ℝ, 0 < c ∧ 0 < eps₀ ∧ 0 < a ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
          θ ∈ angleBox N →
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
          s ≠ 0 ∧
          (∀ i, sourceW s (deformedPoint (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam θ i) ∈ continuedRootDomain) ∧
          ‖coordinateProduct (fun i => selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ≤
              Real.exp (-a*lam) ∧
          ‖coordinateProduct (deformedPoint (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam θ)‖ ≤ Real.exp (-(3*τ/2)*lam) := by
  obtain ⟨R,hR,hproduct⟩ := protected_root_product d
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hR
  have hsinb : 0 < Real.sin d.thetaB := d.a_pos
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [Real.pi_pos,d.theta_lt])
  have hS : 0 < 1+Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  let η₀ := min ηA (Real.sin d.thetaB/4)
  let τ₀ := min R (min (1/2:ℝ) ((1+Real.cos d.thetaB)/8))
  refine ⟨η₀,τ₀,lt_min hηA (by positivity),lt_min hR (lt_min (by norm_num) (by positivity)),?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall : η ≤ Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  have hηA' : η ≤ ηA := hηlt.le.trans (min_le_left _ _)
  have hτR : τ < R := hτlt.trans_le (min_le_left _ _)
  have hτsmall : 2*τ ≤ 1 := by
    have hh := hτlt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hτS : 4*τ < 1+Real.cos d.thetaB := by
    have hh := hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨epsK,hepsK,_,K,hK,hKD,hcoverK⟩ :=
    current_regular_center_compact (c₀ := d.c₀) d.angle_relation hsinb hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨cP,a,hcP,ha,hpd⟩ := hproduct K hK hKD α hα τ hτ hτR
  obtain ⟨epsR,hepsR,_,hmargin⟩ := radialDampingMargin_linear hsint hcsmall
  let c := min cP (1/4:ℝ)
  let eps₀ := min epsK (min epsR R)
  have hc : 0 < c := lt_min hcP (by norm_num)
  have heps₀ : 0 < eps₀ := lt_min hepsK (lt_min hepsR hR)
  refine ⟨c,eps₀,a/2,hc,heps₀,half_pos ha,?_⟩
  intro N eps lamStar lam θ q s hN heps hepslt hls hl hl1 hθ hsupport hsd
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let P := occupancy (fun i => f.p (θ i))
  let ρ := P/(N:ℝ)
  let y := deformedPoint f r τ lam θ
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hn2 : 1 ≤ (N:ℝ)^2 := by nlinarith
  have hl0 : 0 ≤ lam := hls.le.trans hl
  have hepsK' : eps ≤ epsK := hepslt.le.trans (min_le_left _ _)
  have hepsR' : eps < epsR := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsR : eps < R := hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hreg := constructedSelector_regular d.thetaB η α hsinb hη hηsmall hα
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨hqp,hqm,hqsin,hallSin,hqch⟩ :=
    constructed_current_support_geometry d.thetaB η α hsinb hη hηsmall hα q hsupport
  have hP : 1 ≤ P := occupancy_named (fun i => hreg.p_nonneg (θ i)) q hqp
  have hPN : P ≤ N := occupancy_le (fun i => hp1 (θ i))
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := (div_le_one hn0).mpr hPN
  have hWform (i : Fin N) : sourceW (radialParameter d.theta eps) (y i) =
      selectedCenterW d.theta d.c₀ f (lam*τ) eps ρ (θ i) := by
    dsimp [y]
    rw [deformedPoint_scale_lambda,deformedPoint_selected_formula]
    rfl
  have hcompact (i : Fin N) (hi : η^2/2 ≤ lowerChord d.thetaB (θ i)) :
      sourceW (radialParameter d.theta eps) (y i) ∈ K := by
    rw [hWform]
    exact hcoverK eps heps.le hepsK' (lam,(ρ,θ i))
      ⟨⟨hl0,hl1⟩,⟨⟨⟨hρ0,hρ1⟩,⟨⟨hθ.1 i,hθ.2 i⟩,hi⟩⟩,hallSin i⟩⟩
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos d.c₀_pos heps]
  have hmarg : r⁻¹-r < (sourceS (radialParameter d.theta eps)).im := by
    have hh := radialRadius_parameter_margin heps (hmargin eps heps hepsR')
    change r⁻¹-r+Real.sin d.theta*eps < _ at hh
    linarith [mul_pos hsint heps]
  have hcenter (i : Fin N) : 0 < (sourceW (radialParameter d.theta eps) (y i)).im := by
    exact (sourceW_upper_of_margin hr hr1 hmarg (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge (by omega) f hr hτ.le hl0 θ _ hreg.p_nonneg hreg.m_nonneg
        hreg.p_zero hreg.m_zero i)
  have hcover (i : Fin N) : sourceW (radialParameter d.theta eps) (y i) ∈ K ∨
      ∃ u : ℝ, |u| < R ∧ y i=plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u := by
    by_cases hi : η^2/2 ≤ lowerChord d.thetaB (θ i)
    · exact Or.inl (hcompact i hi)
    · have hch : lowerChord d.thetaB (θ i) ≤ η^2 := by linarith [sq_nonneg η]
      have hchA : lowerChord d.thetaB (θ i) ≤ ηA^2 := by nlinarith
      have hu := hcoord (θ i) (hθ.1 i) (hθ.2 i) hchA
      obtain ⟨hm,hp⟩ := constructed_lower_core_plateau hsinb hη hηsmall hα hch
      exact Or.inr ⟨θ i+d.thetaB-2*Real.pi,hu,
        deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ i hp hm⟩
  have hsdP : ‖s-radialParameter d.theta eps‖ ≤ cP*lamStar/(N:ℝ)^2 :=
    hsd.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hls.le) (sq_nonneg _))
  obtain ⟨hdom,hZ⟩ := hpd N eps lamStar lam P (θ q) y q s hN heps hepsR hls hl hl1 hP hPN hqsin
    (deformedPoint_upper_anchor f d.c₀ eps τ lam θ q hqp hqm) hcenter (hcompact q hqch) hcover hsdP
  have hsdC : ‖s-radialParameter d.theta eps‖ ≤ c :=
    hsd.trans ((div_le_self (by positivity) hn2).trans (mul_le_of_le_one_right hc.le (hl.trans hl1)))
  have hs : s ≠ 0 := by
    have hncenter : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
    have hhalf := norm_ge_half_of_near_unit hncenter (show ‖s-radialParameter d.theta eps‖ < 1/2 by
      have := min_le_right cP (1/4:ℝ); linarith)
    exact norm_pos_iff.mp (by linarith)
  refine ⟨hs,hdom,hZ,?_⟩
  exact deformed_y_named_attenuation (by omega) f hr.le hr1.le hτ.le hl0 θ q
    hreg.p_nonneg hreg.m_le_one hqp


/-- The actual constructed current, with its complete angular integral, is
holomorphic on the protected disk. No geometric support predicate is assumed. -/
theorem constructed_current_holomorphic_disk (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ : ℝ, 0 < c ∧ 0 < eps₀ ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
          AnalyticOnNhd ℂ (continuedCurrentSlice N (constructedSelector d.thetaB η α)
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
  have hY (θ : Fin N → ℝ) : 1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0 :=
    homotopy_y_gap_nonzero (by omega) f (Real.exp_pos _)
      (Real.exp_lt_one_iff.mpr (by have := d.c₀_pos; nlinarith)) hτ.le hl0.le θ
      hreg.p_nonneg hreg.m_le_one
  have hZ (s : ℂ) (hs : s ∈ U) (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0 := by
    have hz := (hsource s hs q θ hθ).2.2.1.trans_lt
      (Real.exp_lt_one_iff.mpr (show -a*lam < 0 by nlinarith))
    intro he
    rw [sub_eq_zero.mp he |>.symm,norm_one] at hz
    exact lt_irrefl _ hz
  have hnamed (q : Fin N) : AnalyticOnNhd ℂ
      (continuedNamedCurrentIntegral N f r τ lam q) U :=
    continuedNamedCurrentIntegral_analyticOn_of_gaps N f (Real.exp_pos _).ne' τ lam q
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
end IsingBulk.Tail
