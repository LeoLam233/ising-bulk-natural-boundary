import IsingBulk.Preferred22.SelectedDerivativeAssembly
import IsingBulk.Preferred22.SelectedProfileConvolution
import IsingBulk.Preferred22.SelectedFactorialEstimate

/-! Assembly of the exact manuscript selected-population estimate. The
only input still exposed here is the actual continued kernel determinant
estimate; roots, product gap, one-body majorant, constrained convolution,
normalization and all complex derivative estimates are proved. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 1600000

def PreferredSelectedKernelDiskEstimate (d : PreferredBranchData)
    (cap : ℝ) (hcap : 0<cap) : Prop :=
  let B := cappedCanonicalPreferredBump d cap hcap
  ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ,0<τ → τ<ρ →
    ∃ K : ℝ,0<K ∧ ∀ N : ℕ,2≤N → Even N →
      ∀ ε : ℝ,0<ε → ε<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      (∀ i,AnalyticAt ℂ (preferredSelectedContinuedRoot d B ε τ θ i) t) ∧
      (∀ i l,1-preferredSelectedContinuedRoot d B ε τ θ i t*
        preferredSelectedContinuedRoot d B ε τ θ l t≠0) ∧
      ‖(gaugeKernel (fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i))
        (fun i => preferredSelectedContinuedRoot d B ε τ θ i t)).det‖≤(K*Real.sqrt N)^N

theorem preferred_selected_population_of_kernel_estimate (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) (hkernel : PreferredSelectedKernelDiskEstimate d cap hcap) :
    ∃ ρ : ℝ,0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ,0<τ → τ<ρ →
      PreferredSelectedPopulationBound d (cappedCanonicalPreferredBump d cap hcap) τ ρ := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨ck,ρk,hck,hρk,_hρk1,hkb⟩ := hkernel
  obtain ⟨cp,H,ρp,hcp,hH,hρp,hρp1,hpb⟩ := preferred_selected_continued_product_disk d hcap
  obtain ⟨ca,A,ρa,hca,hA,hρa,_hρa1,hab⟩ := preferred_selected_continued_oneBody_profile d hcap
  obtain ⟨J,hJ,hjac⟩ := preferred_contour_determinant_bound d B
  obtain ⟨D,hD,hprofile⟩ := preferred_selected_profile_constrained_mass d
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
  intro τ hτ hτρ
  obtain ⟨K,hK,hkb'⟩ := hkb τ hτ (hτρ.trans_le hρk')
  have hτ1 : τ≤1 := (hτρ.trans_le hρ1).le
  intro j
  obtain ⟨C,hC,hnum⟩ := preferred_selected_factorial_cauchy_estimate
    (mul_pos (mul_pos hJ hK) hA) hH hD hc hτ j
  refine ⟨C,hC,?_⟩
  intro n hn he ε hε hερ
  let N := n+1
  let R := c*τ^2/(N:ℝ)^3
  let M := (H*(N:ℝ)/τ)*(Real.sqrt N*(J*K*A))^N/(N.factorial:ℝ)
  have hN : 0<N := by dsimp only [N]; omega
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR : 0<R := by dsimp only [R]; positivity
  have hM : 0≤M := by dsimp only [M]; positivity
  have hpoint : ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      AnalyticOnNhd ℂ (preferredSelectedContinuedDensity d B ε τ θ)
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖preferredSelectedContinuedDensity d B ε τ θ t‖≤
          M*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
    intro θ hw
    have hdata (t : ℂ) (ht : t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) := by
      have hdist : ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 := by
        simpa only [Metric.mem_closedBall,dist_eq_norm,R] using ht
      have hmul (b : ℝ) (hcb : c≤b) :
          ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤b*τ^2/(N:ℝ)^3 :=
        hdist.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcb (sq_nonneg _)) (by positivity))
      exact And.intro
        (hkb' N (by dsimp only [N]; omega) he ε hε (hερ.trans_le hρk') θ hw t (hmul ck hck'))
        (And.intro
          (hpb N hN ε τ hε (hερ.trans_le hρp') hτ (hτρ.trans_le hρp') θ hw t (hmul cp hcp'))
          (fun i => hab N hN ε τ hε (hερ.trans_le hρa') hτ (hτρ.trans_le hρa') θ hw t (hmul ca hca') i))
    constructor
    · intro t ht
      obtain ⟨hk,hp,_⟩ := hdata t ht
      apply preferred_selected_continued_density_analyticAt d B ε τ θ t hk.1 hk.2.1
      have hlt : Real.exp (-(cp*τ/(N:ℝ)))<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
      intro hz
      have hz' : preferredSelectedContinuedProduct d B ε τ θ t=1 := (sub_eq_zero.mp hz).symm
      have hh := hp.2.1
      rw [hz',norm_one] at hh
      linarith
    · intro t ht
      obtain ⟨hk,hp,ha⟩ := hdata t ht
      have hb := preferred_selected_continued_density_norm d B ε τ θ t
        (pow_nonneg hJ.le N) (by positivity : 0≤H*(N:ℝ)/τ)
        (by positivity : 0≤(K*Real.sqrt N)^N) hA.le
        (hjac N hN τ hτ.le hτ1 θ) hp.2.2 hk.2.2 (fun i => (ha i).2)
      have hfac : 0<(N.factorial:ℝ) := by positivity
      have hperiod : 1≤(2*Real.pi)^(N-1) :=
        one_le_pow₀ (by linarith [Real.one_le_pi_div_two])
      have hden : (N.factorial:ℝ)≤(N.factorial:ℝ)*(2*Real.pi)^(N-1) :=
        le_mul_of_one_le_right hfac.le hperiod
      have hnonneg : 0≤J^N*(H*(N:ℝ)/τ)*(K*Real.sqrt N)^N*A^N*
          (∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
        have hh : 0≤∏ i,preferredSelectedOneBodyProfile d ε (θ i) :=
          Finset.prod_nonneg (fun i _ => (preferred_selected_oneBody_profile_pos d hε _).le)
        positivity
      calc
        _ ≤ _ := hb
        _ ≤ (J^N*(H*(N:ℝ)/τ)*(K*Real.sqrt N)^N*A^N*
            (∏ i,preferredSelectedOneBodyProfile d ε (θ i)))/(N.factorial:ℝ) :=
          div_le_div_of_nonneg_left hnonneg hfac hden
        _ = _ := by dsimp only [M]; simp only [mul_pow]; ring
  have hbound := preferred_selected_derivative_from_pointwise_disk n d B hε hτ.le hR hM j hpoint
  have hcoef : 0≤(j.factorial:ℝ)*M/R^j := by positivity
  calc
    _ ≤ ((j.factorial:ℝ)*M/R^j)*(∫ θ in angularBox n,
        ∏ i : Fin N,preferredSelectedOneBodyProfile d ε (constrainedAngles θ i)) := hbound
    _ ≤ ((j.factorial:ℝ)*M/R^j)*D^N :=
      mul_le_mul_of_nonneg_left (hprofile n hn ε hε) hcoef
    _ ≤ C*(N:ℝ)^(3*j+1)*(C/Real.sqrt N)^N := hnum N hN

end
end IsingBulk.Preferred22
