import IsingBulk.Preferred22.SelectedKernelCenter
import IsingBulk.Preferred22.SelectedKernelPerturbation
import IsingBulk.Preferred22.SelectedPopulationEstimate
import IsingBulk.Preferred22.SelectedFinitePopulation

/-! Complete actual selected-population kernel estimate on the common
analytic root-continuation disk. The deformation scale is fixed before the
particle number; the unavoidable inverse-square-root tau loss is retained
in its coefficient. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem preferred_selected_kernel_disk_estimate (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) : PreferredSelectedKernelDiskEstimate d cap hcap := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨γ,hγ,hmargin⟩ := cappedCanonicalPreferredBump_sine_margin d hcap
  obtain ⟨a,C,ρC,ha,hC,hρC,hρC1,hcenter⟩ :=
    preferred_selected_center_rows_all_angles d B hγ hmargin
  let β := min (1/2:ℝ) (a/12)
  have hβ : 0<β := lt_min (by norm_num) (by positivity)
  have hβ1 : β≤1/2 := min_le_left _ _
  have hβa : β≤a/12 := min_le_right _ _
  obtain ⟨c,ρr,hc,hρr,_hρr1,hrelative⟩ := preferred_selected_root_relative_disk d hcap hβ
  let ρ := min ρC ρr
  have hρ : 0<ρ := lt_min hρC hρr
  have hρ1 : ρ≤1 := (min_le_left _ _).trans hρC1
  change ∃ c ρ : ℝ, _
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro τ hτ hτρ
  let K := Real.sqrt (16*C/τ)
  have hK : 0<K := Real.sqrt_pos.mpr (by positivity)
  have hKsq : K^2=16*C/τ := Real.sq_sqrt (by positivity)
  refine ⟨K,hK,?_⟩
  intro N hN2 _hEven ε hε hερ θ hw t ht
  have hN : 0<N := by omega
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  have hεC : ε<ρC := hερ.trans_le (min_le_left _ _)
  have hτC : τ<ρC := hτρ.trans_le (min_le_left _ _)
  have hεr : ε<ρr := hερ.trans_le (min_le_right _ _)
  have hτr : τ<ρr := hτρ.trans_le (min_le_right _ _)
  obtain ⟨hpair,hrow⟩ := hcenter N hN ε τ hε hεC hτ hτC θ hw
  have hrel := hrelative N hN ε τ hε hεr hτ hτr θ hw t ht
  let y := preferredSelectedAngularRoot d B τ θ
  let z := preferredSelectedCenterRoot d B ε τ θ
  let z' : Fin N → ℂ := fun i => preferredSelectedContinuedRoot d B ε τ θ i t
  let δ := β*τ/(N:ℝ)^2
  let D := a*τ/(N:ℝ)
  have hδ : 0≤δ := by dsimp only [δ]; positivity
  have hD : 0<D := by dsimp only [D]; positivity
  have hpow : (N:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hδsmall : δ≤β*τ/(N:ℝ) :=
    div_le_div_of_nonneg_left (by positivity : 0≤β*τ) hNr hpow
  have hδ1 : δ≤1 := by
    have hh : β*τ/(N:ℝ)≤β := by
      apply (div_le_iff₀ hNr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hτ1 hβ.le]
    linarith
  have hδD : 6*δ≤D := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hβa hτ.le) hNr.le
    calc
      _ ≤ 6*(β*τ/(N:ℝ)) := mul_le_mul_of_nonneg_left hδsmall (by norm_num)
      _ ≤ 6*((a/12)*τ/(N:ℝ)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = D/2 := by dsimp only [D]; ring
      _ ≤ D := by linarith
  have hzn (i : Fin N) : z i≠0 := physicalRoot_ne_zero _
  have hz1 (i : Fin N) : ‖z i‖≤1 := by
    apply (physicalRoot_inside (Or.inl (ne_of_gt ?_))).le
    exact (mul_pos hε (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
      (by linarith [d.alpha_lt,Real.pi_pos]))).trans_le
      (preferredActualW_im_lower d B hε.le hτ.le θ i)
  have hpair' (i j : Fin N) : 1-z' i*z' j≠0 ∧
      ‖gaugeKernel y z' i j‖^2≤16*‖gaugeKernel y z i j‖^2 :=
    preferred_gaugeKernel_relative_squared_bound y z z' i j (hzn i) (hzn j)
      (hz1 i) (hz1 j) hδ hδ1 hD hδD (hpair i j) (hrel i).2 (hrel j).2
  refine ⟨fun i => (hrel i).1,fun i j => (hpair' i j).1,?_⟩
  apply preferred_determinant_of_row_squares hN (gaugeKernel y z') hK.le
  intro i
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hpair' i j).2)
  rw [←Finset.mul_sum] at hs
  calc
    _ ≤ 16*(∑ j,‖gaugeKernel y z i j‖^2) := hs
    _ ≤ 16*(C*(N:ℝ)/τ) := mul_le_mul_of_nonneg_left (hrow i) (by norm_num)
    _ = K^2*(N:ℝ) := by rw [hKsq]; ring

/-- The manuscript selected-population estimate is now an unconditional
source theorem; all determinant, root-sheet, convolution, and differentiated
normalization inputs are established by the Preferred22 proof chain. -/
theorem preferred_actual_selected_population_bound (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ,0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ,0<τ → τ<ρ →
      PreferredSelectedPopulationBound d (cappedCanonicalPreferredBump d cap hcap) τ ρ :=
  preferred_selected_population_of_kernel_estimate d hcap
    (preferred_selected_kernel_disk_estimate d hcap)

theorem preferred_actual_selected_finite_orders (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ,0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ,0<τ → τ<ρ →
      ∀ n : ℕ,2≤n+1 → Even (n+1) → ∀ j : ℕ,∃ C : ℝ,0<C ∧
      ∀ ε : ℝ,0<ε → ε<ρ →
      ‖iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C :=
  preferred_selected_finite_orders_of_kernel_estimate d hcap
    (preferred_selected_kernel_disk_estimate d hcap)

end
end IsingBulk.Preferred22
