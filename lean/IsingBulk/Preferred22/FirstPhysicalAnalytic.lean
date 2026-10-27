import IsingBulk.Preferred22.FirstLocalAsymptotic
import IsingBulk.First.ActualPostMeanLocalRegularity

/-! Actual parameter analyticity of the normalized physical local chart.
The equality with the published project's proper local residue calculation
holds on an open physical neighborhood, so it transfers analytic germs. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000

theorem preferred_localized_physical_analytic_radial {n : ℕ} (he : Even (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi/2)
    (ha : Complex.exp (-(n+1:ℂ)*(α:ℂ)*Complex.I)=1) :
    ∃ R : ℝ,0<R ∧ ∀ χ : IsingBulk.First.ShapeSpace n → ℂ,
      Continuous χ → (∀ x,χ x≠0 → ‖x‖<R) →
      ∀ ε : ℝ,0<ε → ε<R →
        AnalyticAt ℂ (localizedPhysicalIntegral α χ)
          ((1+(ε:ℂ))*Complex.exp ((α:ℂ)*Complex.I)) := by
  let a := equalAngleData α hα hαπ
  obtain ⟨RA,hRA,hA⟩ := IsingBulk.First.actual_postMean_local_regularity (n := n) a ha ha
  obtain ⟨RB,hRB,hB⟩ := localizedPhysicalIntegral_eq_postMean he α hα hαπ ha
  refine ⟨min RA RB,lt_min hRA hRB,?_⟩
  intro χ hχ hsupp ε hε hεR
  let ζ := Complex.exp ((α:ℂ)*Complex.I)
  let s := (1+(ε:ℂ))*ζ
  have hζ : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I α
  have hεA : ε<RA := hεR.trans_le (min_le_left _ _)
  have hεB : ε<RB := hεR.trans_le (min_le_right _ _)
  have hAi : AnalyticAt ℂ (IsingBulk.First.intrinsicPostMeanIntegral a χ) s := by
    simpa only [IsingBulk.Branch.radialParameter,a,equalAngleData,Complex.ofReal_add,
      Complex.ofReal_one,s,ζ] using
      (hA ε hε hεA χ hχ (fun x hx => (hsupp x hx).trans_le (min_le_left _ _))).1
  have hpost : AnalyticAt ℂ (IsingBulk.First.localizedPostMeanIntegral a χ) s := by
    have hf : IsingBulk.First.localizedPostMeanIntegral a χ=
        fun t => ((Real.sqrt (n+1))⁻¹:ℂ)*IsingBulk.First.intrinsicPostMeanIntegral a χ t := by
      funext t
      rw [IsingBulk.First.localizedPostMeanIntegral_eq_intrinsic,Complex.real_smul,Complex.ofReal_inv]
    rw [hf]
    exact analyticAt_const.mul hAi
  let U : Set ℂ := Metric.ball ζ RB ∩ {t : ℂ | 1<‖t‖} ∩ {t : ℂ | 0<t.im}
  have hU : IsOpen U := (Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hdist : ‖s-ζ‖=ε := by
    rw [show s-ζ=(ε:ℂ)*ζ by dsimp only [s]; ring,norm_mul,hζ,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have hζi : 0<ζ.im := by
    have hh := a.sin_alpha_pos
    change 0<Real.sin α at hh
    simpa only [ζ,Complex.exp_mul_I,Complex.add_im,Complex.cos_ofReal_im,
      Complex.mul_im,Complex.sin_ofReal_re,Complex.I_im,mul_one,
      Complex.sin_ofReal_im,Complex.I_re,mul_zero,zero_add,add_zero] using hh
  have hsU : s∈U := by
    refine ⟨⟨?_,radialPath_exterior hζ hε⟩,?_⟩
    · simpa only [Metric.mem_ball,dist_eq_norm,hdist] using hεB
    · change 0<((1+(ε:ℂ))*ζ).im
      simpa only [Complex.mul_im,Complex.add_re,Complex.one_re,Complex.ofReal_re,
        Complex.add_im,Complex.one_im,Complex.ofReal_im,zero_add,zero_mul,add_zero]
        using mul_pos (show (0:ℝ)<1+ε by linarith) hζi
  have heq : localizedPhysicalIntegral α χ=ᶠ[𝓝 s] IsingBulk.First.localizedPostMeanIntegral a χ := by
    filter_upwards [hU.mem_nhds hsU] with t ht
    exact hB χ (fun x hx => (hsupp x hx).trans_le (min_le_right _ _)) t
      (by simpa only [Metric.mem_ball,dist_eq_norm] using ht.1.1) ht.1.2 ht.2
  exact hpost.congr heq.symm

end
end IsingBulk.Preferred22
