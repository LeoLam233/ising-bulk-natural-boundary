import IsingBulk.HT22.Physical.Holomorphy
import IsingBulk.First.ExteriorIdentitySymmetry
import IsingBulk.HT22.First.LocalLimit.TwoCharts

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter IsingBulk.First IsingBulk.Branch
open scoped Topology

def oneParticleRational (negative : Bool) (t : ℂ) : ℂ :=
  t/(t-Physical.constraintSign negative)^2

theorem oneParticleRational_analyticAt (negative : Bool) {t : ℂ}
    (ht : t≠Physical.constraintSign negative) :
    AnalyticAt ℂ (oneParticleRational negative) t := by
  exact analyticAt_id.div ((analyticAt_id.sub analyticAt_const).pow 2)
    (pow_ne_zero _ (sub_ne_zero.mpr ht))

theorem oneParticle_eq_exterior (negative : Bool) :
    EqOn (Physical.signedCoefficient negative 1) (oneParticleRational negative)
      {t : ℂ | 1<‖t‖} := by
  apply exterior_eq_of_real_ray (by norm_num : (0:ℝ)≤1)
    (fun t ht => Physical.signedCoefficient_analyticAt negative 1 ht)
  · intro t ht
    apply oneParticleRational_analyticAt
    intro he
    change 1<‖t‖ at ht
    rw [he,Physical.constraintSign_norm] at ht
    exact (lt_irrefl 1 ht)
  · intro x hx
    have hx0 : x≠0 := by linarith
    cases negative
    · change Physical.coefficient 1 (x:ℂ)=_
      rw [Physical.coefficient_one_real hx]
      unfold oneParticleRational Physical.constraintSign
      simp only [Bool.false_eq_true,↓reduceIte]
      norm_cast
      have he : x+x⁻¹-2=(x-1)^2/x := by field_simp;ring
      rw [he,inv_div]
    · rw [Physical.signedCoefficient_one_negative_real hx]
      unfold oneParticleRational Physical.constraintSign
      simp only [↓reduceIte,sub_neg_eq_add]
      norm_cast
      have he : x+x⁻¹+2=(x+1)^2/x := by field_simp;ring
      rw [he,inv_div]

theorem oneParticleRational_derivative_analyticAt (negative : Bool) {t : ℂ}
    (ht : t≠Physical.constraintSign negative) (j : ℕ) :
    AnalyticAt ℂ (deriv^[j] (oneParticleRational negative)) t := by
  induction j with
  | zero => exact oneParticleRational_analyticAt negative ht
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv

/-- All fixed derivatives of the actual signed one-particle term are
negligible at the epsilon^{-1} scale away from their true poles ±1. -/
theorem oneParticle_radial_derivative_limit (negative : Bool) (α : ℝ)
    (hα : exp ((α:ℂ)*I)≠Physical.constraintSign negative) (j : ℕ) :
    Tendsto (fun ε : ℝ => ε •
      (deriv^[j] (Physical.signedCoefficient negative 1)) (radialParameter α ε))
      (𝓝[>] 0) (𝓝 0) := by
  have hrad : Tendsto (radialParameter α) (𝓝[>] 0) (𝓝 (exp ((α:ℂ)*I))) := by
    have hcont : Continuous (radialParameter α) := by unfold radialParameter;fun_prop
    simpa [radialParameter] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr := (oneParticleRational_derivative_analyticAt negative hα j).continuousAt.tendsto.comp hrad
  have ht := (tendsto_id.mono_left nhdsWithin_le_nhds).smul hr
  simp only [zero_smul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε he
  have hnrm : 1<‖radialParameter α ε‖ := by
    rw [radialParameter_norm he.le];exact lt_add_of_pos_right 1 he
  have heq : Physical.signedCoefficient negative 1 =ᶠ[𝓝 (radialParameter α ε)]
      oneParticleRational negative := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hnrm] with z hz
    exact oneParticle_eq_exterior negative hz
  have hd := heq.iteratedDeriv_eq j
  simp only [iteratedDeriv_eq_iterate] at hd
  exact congrArg (fun z : ℂ => ε • z) hd.symm

/-- F001's separate finite-order n=1 estimate is genuinely bounded, hence
satisfies the stated logarithmic envelope for both signed constraints. -/
theorem oneParticle_radial_derivative_bound (negative : Bool) (α : ℝ)
    (hα : exp ((α:ℂ)*I)≠Physical.constraintSign negative) (j : ℕ) :
    ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ‖(deriv^[j] (Physical.signedCoefficient negative 1)) (radialParameter α ε)‖≤
        C*(1+|Real.log ε|) := by
  have hrad : Tendsto (radialParameter α) (𝓝[>] 0) (𝓝 (exp ((α:ℂ)*I))) := by
    have hcont : Continuous (radialParameter α) := by unfold radialParameter;fun_prop
    simpa [radialParameter] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr := (oneParticleRational_derivative_analyticAt negative hα j).continuousAt.tendsto.comp hrad
  let C := ‖(deriv^[j] (oneParticleRational negative)) (exp ((α:ℂ)*I))‖+1
  have hC : 0<C := by dsimp [C];positivity
  have hev := hr.norm.eventually (Iio_mem_nhds (show
    ‖(deriv^[j] (oneParticleRational negative)) (exp ((α:ℂ)*I))‖<C by dsimp [C];linarith))
  obtain ⟨ε₀,hε₀,hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro ε he he0
  have hnrm : 1<‖radialParameter α ε‖ := by
    rw [radialParameter_norm he.le];exact lt_add_of_pos_right 1 he
  have heq : Physical.signedCoefficient negative 1 =ᶠ[𝓝 (radialParameter α ε)]
      oneParticleRational negative := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hnrm] with z hz
    exact oneParticle_eq_exterior negative hz
  have hd := heq.iteratedDeriv_eq j
  simp only [iteratedDeriv_eq_iterate] at hd
  rw [hd]
  have hsmall : ‖(deriv^[j] (oneParticleRational negative)) (radialParameter α ε)‖<C := hb ⟨he,he0⟩
  have hlog : 0≤|Real.log ε| := abs_nonneg _
  nlinarith

end
end IsingBulk.HT22.LocalLimit
