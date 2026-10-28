import IsingBulk.HT22.First.LocalLimit.TwoCharts

/-! Nonresonant equality neighborhoods in the finite complement really
extend holomorphically. Only geometric data and the literal product gap enter. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Branch
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

theorem nonresonant_residue_analyticAt (a : RegularChartData) (N : ℕ)
    (hb : exp (-(N:ℂ)*(a.beta:ℂ)*I)≠1) :
    AnalyticAt ℂ (@complexPostMeanResidue N a.alpha)
      (exp ((a.theta:ℂ)*I),(0:Fin N → ℂ)) := by
  have hden : complexDensityDenominator a.alpha
      (exp ((a.theta:ℂ)*I),(0:Fin N → ℂ))≠0 := by
    unfold complexDensityDenominator
    simp only [Regular.complexDensityZ_center,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [←exp_nat_mul]
    apply sub_ne_zero.mpr
    intro he
    apply hb
    convert he.symm using 1
    congr 1
    ring
  exact ((analyticAt_const.mul (Regular.complexMeanNumerator_analyticAt a N)).div
    (Regular.complexDensityDenominator_analyticAt a N) hden).div_const

theorem nonresonant_local_integral_analyticAt {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)≠1) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ, Continuous χ →
      (∀ x,χ x≠0 → ‖x‖<R) →
      AnalyticAt ℂ (Regular.localizedPostMeanIntegral a χ) (exp ((a.theta:ℂ)*I)) := by
  let s₀ := exp ((a.theta:ℂ)*I)
  let g := fun p : ℂ × ShapeSpace n => (p.1,intrinsicComplexShape p.2)
  have hg : Continuous g := continuous_fst.prodMk
    ((intrinsicComplexShape_continuous n).comp continuous_snd)
  have hzero : g (s₀,0)=(s₀,(0:Fin (n+1) → ℂ)) := rfl
  have ht := hg.tendsto (s₀,0)
  rw [hzero] at ht
  have hev := ht.eventually ((nonresonant_residue_analyticAt a (n+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hb)).eventually_analyticAt)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
  let R := r/2
  have hR : 0<R := half_pos hr
  have hRr : R<r := half_lt_self hr
  refine ⟨R,hR,?_⟩
  intro χ hχ hχs
  let K := Metric.closedBall (0:ShapeSpace n) R
  have hF (s : ℂ) (hs : s∈ball s₀ R) (x : ShapeSpace n) (hx : x∈K) :
      AnalyticAt ℂ (complexPostMeanResidue a.alpha) (s,intrinsicComplexShape x) := by
    apply hball (a:=(s,x))
    rw [mem_ball,dist_eq_norm]
    change max ‖s-s₀‖ ‖x-0‖<r
    rw [sub_zero,max_lt_iff]
    refine ⟨?_,?_⟩
    · exact (by simpa only [mem_ball,dist_eq_norm] using hs : ‖s-s₀‖<R).trans hRr
    · exact (by simpa only [K,mem_closedBall,dist_zero_right] using hx : ‖x‖≤R).trans_lt hRr
  have h := compact_analytic_shape_integral_analyticAt (μ := (volume : Measure (ShapeSpace n)))
    (isCompact_closedBall (0:ShapeSpace n) R) isOpen_ball (complexPostMeanResidue a.alpha)
    intrinsicComplexShape (intrinsicComplexShape_continuous n) χ hχ hF (mem_ball_self hR)
  have hzeroχ (x : ShapeSpace n) (hx : x∉K) : χ x=0 := by
    by_contra hh
    apply hx
    exact mem_closedBall_zero_iff.mpr (hχs x hh).le
  have heq : (fun s => ∫ x : ShapeSpace n in K,χ x*complexPostMeanResidue a.alpha (s,intrinsicComplexShape x))=
      Regular.intrinsicPostMeanIntegral a χ := by
    funext s
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzeroχ x hx,zero_mul])]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [Regular.complexPostMeanResidue_intrinsic a ha]
  change AnalyticAt ℂ (fun s => ∫ x : ShapeSpace n in K,χ x*complexPostMeanResidue a.alpha (s,intrinsicComplexShape x)) s₀ at h
  rw [heq] at h
  have hloc : Regular.localizedPostMeanIntegral a χ=
      fun s => ((Real.sqrt (n+1))⁻¹:ℂ)*Regular.intrinsicPostMeanIntegral a χ s := by
    funext s
    rw [Regular.localizedPostMeanIntegral_eq_intrinsic,Complex.real_smul,ofReal_inv]
  rw [hloc]
  exact analyticAt_const.mul h

/-- Nonresonant constrained equality charts have bounded derivatives of the
actual physical angular integral, not only of a model source. -/
theorem nonresonant_angular_derivatives_bounded {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)≠1) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ, Continuous χ →
      (∀ x,χ x≠0 → ‖x‖<R) → ∀ j : ℕ,
      ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
        ‖(deriv^[j] (angularLocalIntegral a.alpha χ)) (radialParameter a.theta ε)‖≤C := by
  obtain ⟨Ri,hRi,hI⟩ := nonresonant_local_integral_analyticAt a ha hb
  obtain ⟨Ra,hRa,hA⟩ := angularLocalIntegral_deriv_eq_postMean (n:=n) a ha
  refine ⟨min Ri Ra,lt_min hRi hRa,?_⟩
  intro χ hχ hχs j
  have hf := hI χ hχ (fun x hx => (hχs x hx).trans_le (min_le_left _ _))
  have hd : ∀ j : ℕ, AnalyticAt ℂ (deriv^[j] (Regular.localizedPostMeanIntegral a χ))
      (exp ((a.theta:ℂ)*I)) := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih => rw [Function.iterate_succ_apply'];exact ih.deriv
  have hrad : Tendsto (radialParameter a.theta) (𝓝[>] 0) (𝓝 (exp ((a.theta:ℂ)*I))) := by
    have hcont : Continuous (radialParameter a.theta) := by unfold radialParameter;fun_prop
    simpa [radialParameter] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr := (hd j).continuousAt.tendsto.comp hrad
  let C := ‖(deriv^[j] (Regular.localizedPostMeanIntegral a χ)) (exp ((a.theta:ℂ)*I))‖+1
  have hC : 0<C := by dsimp [C];positivity
  have hev := hr.norm.eventually (Iio_mem_nhds (show
    ‖(deriv^[j] (Regular.localizedPostMeanIntegral a χ)) (exp ((a.theta:ℂ)*I))‖<C by dsimp [C];linarith))
  obtain ⟨ε₀,hε₀,hbnd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro ε he he0
  have hnrm : 1<‖radialParameter a.theta ε‖ := by
    rw [radialParameter_norm he.le];exact lt_add_of_pos_right 1 he
  rw [hA χ (fun x hx => (hχs x hx).trans_le (min_le_right _ _))
    (radialParameter a.theta ε) hnrm (radial_source_upper a.sin_theta_pos he) j]
  exact (hbnd ⟨he,he0⟩).le

end
end IsingBulk.HT22.LocalLimit
