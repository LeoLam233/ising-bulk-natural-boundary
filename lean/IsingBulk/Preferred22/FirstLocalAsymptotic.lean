import IsingBulk.Preferred22.FirstChart
import IsingBulk.Preferred22.NaturalBoundary

/-! Local first-singularity asymptotics for the literal Preferred physical
angular integral, with the physical branch/domain bridge proved. This remains
a local-chart theorem; identifying the entire C_N requires the finite complement. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set Filter Metric MeasureTheory
open scoped BigOperators Topology

theorem angularW_im_pos {s : ℂ} (hs : 1 < ‖s‖) (hi : 0 < s.im) (θ : ℝ) :
    0 < (angularW s θ).im := by
  have hnorm : 1 < Complex.normSq s := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  have hfrac : s.im/Complex.normSq s < s.im := (div_lt_self hi hnorm)
  simpa only [angularW,temperatureTrace,Complex.sub_im,Complex.add_im,
    Complex.ofReal_im,sub_zero,Complex.inv_im,neg_div,← sub_eq_add_neg] using sub_pos.mpr hfrac

theorem firstChart_domain_neighborhood (n : ℕ) (α : ℝ) (hα : 0 < α)
    (hαπ : α < Real.pi/2) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℂ, ‖s-exp ((α:ℂ)*I)‖ < R →
      ∀ t : Fin n → ℝ, ‖t‖ < R →
        (∀ j, 0 < (angularW s (firstChartAngles α t j)).re) ∧
        (∀ i j, 1-angleRoot (firstChartAngles α t i)*angleRoot (firstChartAngles α t j) ≠ 0) := by
  let a := equalAngleData α hα hαπ
  let c : ℂ × (Fin n → ℝ) := (exp ((α:ℂ)*I),0)
  have hpos : ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 c,
      ∀ j, 0 < (angularW p.1 (firstChartAngles α p.2 j)).re := by
    apply Filter.eventually_all.mpr
    intro j
    have heq (p : ℂ × (Fin n → ℝ)) :
        angularW p.1 (firstChartAngles α p.2 j)=
          IsingBulk.First.sourceW p.1 (IsingBulk.First.shapeY α p.2 j) := by
      rw [firstChart_shapeY,sourceW_angleRoot]
    simp_rw [heq]
    have hc : ContinuousAt (fun p : ℂ × (Fin n → ℝ) =>
        (IsingBulk.First.sourceW p.1 (IsingBulk.First.shapeY α p.2 j)).re) c := by
      have hz : c.1 ≠ 0 := exp_ne_zero _
      have hy : Continuous (fun p : ℂ × (Fin n → ℝ) =>
          IsingBulk.First.shapeY α p.2 j) := by
        unfold IsingBulk.First.shapeY
        exact (((Complex.continuous_ofReal.comp
          ((IsingBulk.First.continuous_shapeExtend_eval j).comp continuous_snd)).sub
          continuous_const).mul continuous_const).cexp
      have ht : ContinuousAt (fun p : ℂ × (Fin n → ℝ) =>
          IsingBulk.First.sourceW p.1 (IsingBulk.First.shapeY α p.2 j)) c :=
        (continuous_fst.continuousAt.add (continuous_fst.continuousAt.inv₀ hz)).sub
          ((hy.continuousAt.add (hy.continuousAt.inv₀ (exp_ne_zero _))).div_const 2)
      exact Complex.continuous_re.continuousAt.comp ht
    have hcenter : IsingBulk.First.sourceW c.1 (IsingBulk.First.shapeY α c.2 j)=
        (Real.cos α:ℂ) := by
      dsimp only [c]
      rw [IsingBulk.First.shapeY_zero_exact]
      exact IsingBulk.First.sourceW_density_center a
    apply hc.eventually (Ioi_mem_nhds _)
    change 0 < (IsingBulk.First.sourceW c.1 (IsingBulk.First.shapeY α c.2 j)).re
    rw [hcenter,Complex.ofReal_re]
    exact a.cos_alpha_pos
  have hdom := IsingBulk.First.actualDensityDomain_eventually a n
  change ∀ᶠ p in 𝓝 c, IsingBulk.First.ActualDensityDomain a n p at hdom
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp (hpos.and hdom)
  refine ⟨R,hR,?_⟩
  intro s hs t ht
  have hd : dist (s,t) c < R := by
    rw [dist_eq_norm,Prod.norm_def]
    simpa only [Prod.fst_sub,Prod.snd_sub,c,sub_zero] using max_lt hs ht
  have hh := hball hd
  refine ⟨hh.1,?_⟩
  intro i j
  have hy := hh.2.2.2.1 i j
  change 1-IsingBulk.First.shapeY α t i*IsingBulk.First.shapeY α t j ≠ 0 at hy
  rwa [firstChart_shapeY] at hy

theorem free_norm_le_shape_norm {n : ℕ} (t : Fin n → ℝ) :
    ‖t‖ ≤ ‖IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa using PiLp.norm_apply_le
    (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)).1 i.castSucc

theorem localizedPhysicalIntegral_eq_postMean {n : ℕ} (he : Even (n+1))
    (α : ℝ) (hα : 0 < α) (hαπ : α < Real.pi/2)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : IsingBulk.First.ShapeSpace n → ℂ,
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ s : ℂ, ‖s-exp ((α:ℂ)*I)‖ < R → 1 < ‖s‖ → 0 < s.im →
        localizedPhysicalIntegral α chi s=
          IsingBulk.First.localizedPostMeanIntegral (equalAngleData α hα hαπ) chi s := by
  obtain ⟨R,hR,hdom⟩ := firstChart_domain_neighborhood n α hα hαπ
  refine ⟨R,hR,?_⟩
  intro chi hchi s hs hsx hsi
  unfold localizedPhysicalIntegral IsingBulk.First.localizedPostMeanIntegral
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  by_cases hct : chi (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))=0
  · simp only [hct,zero_mul]
  · have ht : ‖t‖ < R := (free_norm_le_shape_norm t).trans_lt (hchi _ hct)
    obtain ⟨hr,hy⟩ := hdom s hs t ht
    dsimp only [equalAngleData]
    rw [postMeanDensity_eq_preferred he hsx α t ha hr
      (fun j => angularW_im_pos hsx hsi _) (fun i j _ => hy i j)]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

/-- The exact local differentiated first-singularity asymptotic, for the
physical-root integral defined in FirstChart, with a nonzero coefficient. -/
theorem localizedPhysical_source_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (he : Even (n+1)) (α : ℝ) (hα : 0 < α) (hαπ : α < Real.pi/2)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    let k := (n+1)^2/2-1
    let a := equalAngleData α hα hαπ
    IsingBulk.First.localLeadingCoefficient a n k ≠ 0 ∧
    ∃ R : ℝ, 0 < R ∧ ∀ chi : IsingBulk.First.ShapeSpace n → ℂ,
      Continuous chi → chi 0=1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun eps => iteratedDeriv k (localizedPhysicalIntegral α chi)
          ((1+(eps:ℂ))*exp ((α:ℂ)*I))-
            (Real.sqrt eps:ℂ)⁻¹*IsingBulk.First.localLeadingCoefficient a n k)
        (fun eps => (Real.sqrt eps:ℂ)⁻¹) := by
  dsimp only
  let a := equalAngleData α hα hαπ
  obtain ⟨hL,RA,hRA,hA⟩ := IsingBulk.First.actual_localized_postMean_source_asymptotic
    hn a he ha ha
  obtain ⟨RB,hRB,hB⟩ := localizedPhysicalIntegral_eq_postMean he α hα hαπ ha
  refine ⟨hL,min RA RB,lt_min hRA hRB,?_⟩
  intro chi hchi hc0 hcb hcs
  have hresult := hA chi hchi hc0 hcb (fun x hx => (hcs x hx).trans_le (min_le_left _ _))
  have hsupport : ∀ x, chi x ≠ 0 → ‖x‖ < RB :=
    fun x hx => (hcs x hx).trans_le (min_le_right _ _)
  let ζ := exp ((α:ℂ)*I)
  let U : Set ℂ := ball ζ RB ∩ {s : ℂ | 1 < ‖s‖} ∩ {s : ℂ | 0 < s.im}
  have hU : IsOpen U := (isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have heq : EqOn (localizedPhysicalIntegral α chi)
      (IsingBulk.First.localizedPostMeanIntegral a chi) U := by
    intro s hs
    exact hB chi hsupport s (by simpa only [mem_ball,dist_eq_norm] using hs.1.1) hs.1.2 hs.2
  have hζnorm : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I α
  have hζim : 0 < ζ.im := by
    have hsα : 0 < Real.sin α := a.sin_alpha_pos
    simpa only [ζ,Complex.exp_mul_I,Complex.add_im,Complex.cos_ofReal_im,
      Complex.mul_im,Complex.sin_ofReal_re,Complex.I_im,mul_one,
      Complex.sin_ofReal_im,Complex.I_re,mul_zero,zero_add,add_zero] using hsα
  have hpath (eps : ℝ) : IsingBulk.Branch.radialParameter a.theta eps=(1+(eps:ℂ))*ζ := by
    simp only [IsingBulk.Branch.radialParameter,a,equalAngleData,ζ,ofReal_add,ofReal_one]
  apply hresult.congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [(radialPath_tendsto ζ).eventually (ball_mem_nhds ζ hRB),self_mem_nhdsWithin]
    with eps heball he
  have hep : 0 < eps := he
  rw [hpath]
  congr 1
  have hsU : (1+(eps:ℂ))*ζ ∈ U := by
    refine ⟨⟨heball,radialPath_exterior hζnorm he⟩,?_⟩
    change 0 < ((1+(eps:ℂ))*ζ).im
    simpa only [Complex.mul_im,Complex.add_re,Complex.one_re,Complex.ofReal_re,
      Complex.add_im,Complex.one_im,Complex.ofReal_im,zero_add,zero_mul,add_zero]
      using mul_pos (show (0:ℝ)<1+eps by linarith) hζim
  have hder := (heq.eventuallyEq_of_mem (hU.mem_nhds hsU)).iteratedDeriv_eq (n := (n+1)^2/2-1)
  simpa only [iteratedDeriv_eq_iterate] using hder.symm

end
end IsingBulk.Preferred22
