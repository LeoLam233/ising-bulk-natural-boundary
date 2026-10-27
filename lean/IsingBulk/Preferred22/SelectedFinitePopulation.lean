import IsingBulk.Preferred22.SelectedPopulationEstimate
import IsingBulk.Preferred22.SelectedUniformOneBody

/-! The selected sector at each fixed positive even particle order,
including two. This uses the actual displaced branch gap and compact angular
volume, and hence needs no fourfold convolution at order two. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem preferred_selected_derivative_from_constant_disk (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ R M : ℝ} (hε : 0<ε) (hτ : 0≤τ) (hR : 0<R) (hM : 0≤M) (j : ℕ)
    (hpoint : ∀ θ : Fin (n+1) → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      AnalyticOnNhd ℂ (preferredSelectedContinuedDensity d B ε τ θ)
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖preferredSelectedContinuedDensity d B ε τ θ t‖≤M) :
    ‖iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤((j.factorial:ℝ)*M/R^j)*(2*Real.pi)^n := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let w := fun θ : Fin (n+1) → ℝ =>
    (preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ:ℂ)
  have hw : Continuous w := by
    have hp := B.smooth.continuous
    have hm := B.m_smooth.continuous
    have hη := preferredPopulationCutoff_smooth.continuous
    unfold w preferredFullPopulationWeight fullWeight occupancy
    fun_prop
  obtain ⟨heq,_⟩ := preferred_weighted_contour_integral_jets n d B hτ w hw
    (preferredRadialTrace_im_pos d hε) j
  change iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m) s = _ at heq
  rw [heq,←angularBox_volume_real]
  apply norm_setIntegral_le_of_norm_le_const_ae
    (by rw [angularBox_volume]; exact ENNReal.ofReal_lt_top)
  filter_upwards [] with θ
  let x := constrainedAngles θ
  by_cases hx : preferredFullPopulationWeight preferredPopulationCutoff B.p B.m x=0
  · have hwx : w x=0 := by simp [w,hx]
    change ‖iteratedDeriv j (fun t : ℂ => w x*preferredBareContourDensity τ B.p B.m t x) s‖≤_
    simp only [hwx,zero_mul,iteratedDeriv_fun_const_zero,norm_zero]
    positivity
  · obtain ⟨ha,hb⟩ := hpoint x hx
    have hbound := IsingBulk.First.cauchy_bound_on_subdisk ha hb hR (Subset.rfl) j
    have hgerm := preferred_selected_continued_density_germ d B hε hτ x
    change ‖iteratedDeriv j (fun t : ℂ => w x*preferredBareContourDensity τ B.p B.m t x) s‖≤_
    rw [iteratedDeriv_const_mul_field,←hgerm.iteratedDeriv_eq,norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (preferred_selected_weight_norm_le_one B.p B.m x) (norm_nonneg _)).trans (by simpa using hbound)

theorem preferred_selected_finite_orders_of_kernel_estimate (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) (hkernel : PreferredSelectedKernelDiskEstimate d cap hcap) :
    ∃ ρ : ℝ,0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ,0<τ → τ<ρ →
      ∀ n : ℕ,2≤n+1 → Even (n+1) → ∀ j : ℕ,∃ C : ℝ,0<C ∧
      ∀ ε : ℝ,0<ε → ε<ρ →
      ‖iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨ck,ρk,hck,hρk,_hρk1,hkb⟩ := hkernel
  obtain ⟨cp,H,ρp,hcp,hH,hρp,hρp1,hpb⟩ := preferred_selected_continued_product_disk d hcap
  obtain ⟨ca,ρa,hca,hρa,_hρa1,hab⟩ := preferred_selected_continued_oneBody_uniform d hcap
  obtain ⟨J,hJ,hjac⟩ := preferred_contour_determinant_bound d B
  let c := min cp (min ca ck)
  let ρ := min ρp (min ρa ρk)
  have hc : 0<c := lt_min hcp (lt_min hca hck)
  have hρ : 0<ρ := lt_min hρp (lt_min hρa hρk)
  have hρp' : ρ≤ρp := min_le_left _ _
  have hρa' : ρ≤ρa := (min_le_right _ _).trans (min_le_left _ _)
  have hρk' : ρ≤ρk := (min_le_right _ _).trans (min_le_right _ _)
  have hcp' : c≤cp := min_le_left _ _
  have hca' : c≤ca := (min_le_right _ _).trans (min_le_left _ _)
  have hck' : c≤ck := (min_le_right _ _).trans (min_le_right _ _)
  have hρ1 : ρ≤1 := hρp'.trans hρp1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro τ hτ hτρ n hn he j
  obtain ⟨K,hK,hkb'⟩ := hkb τ hτ (hτρ.trans_le hρk')
  have hτ1 : τ≤1 := (hτρ.trans_le hρ1).le
  have hτsq : τ^2≤τ := by nlinarith
  let N := n+1
  let R := c*τ^2/(N:ℝ)^3
  let A := (Real.sqrt (ca*τ/(N:ℝ)))⁻¹
  let M := J^N*(H*(N:ℝ)/τ)*(K*Real.sqrt N)^N*A^N/
    ((N.factorial:ℝ)*(2*Real.pi)^(N-1))
  have hN : 0<N := by dsimp only [N]; omega
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR : 0<R := by dsimp only [R]; positivity
  have hA : 0<A := by dsimp only [A]; positivity
  have hM : 0≤M := by dsimp only [M]; positivity
  refine ⟨((j.factorial:ℝ)*M/R^j)*(2*Real.pi)^n+1,by positivity,?_⟩
  intro ε hε hερ
  have hpoint : ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      AnalyticOnNhd ℂ (preferredSelectedContinuedDensity d B ε τ θ)
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖preferredSelectedContinuedDensity d B ε τ θ t‖≤M := by
    intro θ hw
    have hdata (t : ℂ) (ht : t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) := by
      have hd : ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 := by
        simpa only [Metric.mem_closedBall,dist_eq_norm,R] using ht
      have hm (b : ℝ) (hcb : c≤b) :
          ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤b*τ^2/(N:ℝ)^3 :=
        hd.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcb (sq_nonneg _)) (by positivity))
      have hra : ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤ca*τ/(N:ℝ)^3 :=
        (hm ca hca').trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτsq hca.le) (by positivity))
      exact And.intro (hkb' N hn he ε hε (hερ.trans_le hρk') θ hw t (hm ck hck'))
        (And.intro (hpb N hN ε τ hε (hερ.trans_le hρp') hτ
          (hτρ.trans_le hρp') θ hw t (hm cp hcp'))
          (fun i => hab N hN ε τ hε (hερ.trans_le hρa') hτ
            (hτρ.trans_le hρa') θ hw t hra i))
    constructor
    · intro t ht
      obtain ⟨hk,hp,_⟩ := hdata t ht
      apply preferred_selected_continued_density_analyticAt d B ε τ θ t hk.1 hk.2.1
      have hlt : Real.exp (-(cp*τ/(N:ℝ)))<1 :=
        Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
      intro hz
      have hz' : preferredSelectedContinuedProduct d B ε τ θ t=1 := (sub_eq_zero.mp hz).symm
      have hh := hp.2.1
      rw [hz',norm_one] at hh
      linarith
    · intro t ht
      obtain ⟨hk,hp,ha⟩ := hdata t ht
      have hb : ‖∏ i,oneBody (preferredSelectedContinuedRoot d B ε τ θ i t)‖≤A^N := by
        rw [norm_prod]
        exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => (ha i).2)).trans_eq
          (by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl)
      have hnum := mul_le_mul (mul_le_mul
        (mul_le_mul (hjac N hN τ hτ.le hτ1 θ) hp.2.2 (norm_nonneg _) (by positivity))
        hk.2.2 (norm_nonneg _) (by positivity)) hb (norm_nonneg _) (by positivity)
      unfold preferredSelectedContinuedDensity
      rw [norm_div]
      simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [preferredSelectedContinuedProduct,M,mul_assoc] using hnum
  have hb := preferred_selected_derivative_from_constant_disk n d B hε hτ.le hR hM j hpoint
  exact hb.trans (by linarith)

end
end IsingBulk.Preferred22
