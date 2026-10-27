import IsingBulk.Preferred22.SelectedProductDisk
import IsingBulk.Preferred22.SelectedOneBodyDisk
import IsingBulk.Preferred22.WeightedIntegralJets

/-! The genuine selected-sheet continuation of the complete normalized
contour integrand, with its exact physical germ and rational determinant
analyticity. The real angular weights remain fixed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped BigOperators Topology
set_option maxHeartbeats 1200000

def preferredSelectedContinuedDensity {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ) : ℂ :=
  let z := fun i => preferredSelectedContinuedRoot d B ε τ θ i t
  let y := fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)
  (preferredContourMatrix τ B.p B.m θ).det *
    (((1+∏ i,z i)/(1-∏ i,z i))*(gaugeKernel y z).det*∏ i,oneBody (z i)) /
      ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

theorem preferred_selected_continued_density_germ {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (θ : Fin N → ℝ) :
    preferredSelectedContinuedDensity d B ε τ θ =ᶠ[𝓝 (IsingBulk.Branch.radialParameter d.alpha ε)]
      (fun t => preferredBareContourDensity τ B.p B.m t θ) := by
  have hz : ∀ᶠ t in 𝓝 (IsingBulk.Branch.radialParameter d.alpha ε),∀ i : Fin N,
      preferredSelectedContinuedRoot d B ε τ θ i t =
        physicalRoot (temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i)) :=
    eventually_all.mpr (fun i => preferred_selected_continued_root_germ d B hε hτ θ i)
  filter_upwards [hz] with t ht
  simp only [preferredSelectedContinuedDensity,preferredBareContourDensity,
    preferredDeformedPhysicalDensity,ht]

theorem preferred_selected_continued_density_analyticAt {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ)
    (hroot : ∀ i,AnalyticAt ℂ (preferredSelectedContinuedRoot d B ε τ θ i) t)
    (hpair : ∀ i j,1-preferredSelectedContinuedRoot d B ε τ θ i t*
      preferredSelectedContinuedRoot d B ε τ θ j t≠0)
    (hprod : 1-preferredSelectedContinuedProduct d B ε τ θ t≠0) :
    AnalyticAt ℂ (preferredSelectedContinuedDensity d B ε τ θ) t := by
  let z := fun s i => preferredSelectedContinuedRoot d B ε τ θ i s
  let y := fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)
  have hZ := Finset.univ.analyticAt_fun_prod (fun i _ => hroot i)
  have hR (i j : Fin N) : AnalyticAt ℂ (fun s => rationalKernel y (z s) i j) t :=
    (analyticAt_const.sub analyticAt_const).div
      (analyticAt_const.sub ((hroot i).mul (hroot j))) (hpair i j)
  have hdet : AnalyticAt ℂ (fun s => (rationalKernel y (z s)).det) t := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hR (σ i) i)))
  have hratio : AnalyticAt ℂ (fun s => ∏ i,z s i/y i) t :=
    Finset.univ.analyticAt_fun_prod (fun i _ => (hroot i).div_const)
  have hbody : AnalyticAt ℂ (fun s => ∏ i,oneBody (z s i)) t := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (analyticAt_const.mul (hroot i)).div (analyticAt_const.sub ((hroot i).pow 2))
    change 1-(preferredSelectedContinuedRoot d B ε τ θ i t)^2≠0
    simpa only [pow_two] using hpair i i
  unfold preferredSelectedContinuedDensity
  change AnalyticAt ℂ (fun s => (preferredContourMatrix τ B.p B.m θ).det *
    (((1+∏ i,z s i)/(1-∏ i,z s i))*(gaugeKernel y (z s)).det*∏ i,oneBody (z s i)) /
      ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))) t
  simp_rw [gaugeKernel_det_normalization]
  exact (analyticAt_const.mul ((((analyticAt_const.add hZ).div
    (analyticAt_const.sub hZ) hprod).mul ((analyticAt_const.mul hratio).mul hdet)).mul hbody)).div_const

theorem preferred_selected_continued_density_norm {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ)
    {J R K A : ℝ} (hJ : 0≤J) (hR : 0≤R) (hK : 0≤K) (_hA : 0≤A)
    (hjac : ‖(preferredContourMatrix τ B.p B.m θ).det‖≤J)
    (hres : ‖(1+preferredSelectedContinuedProduct d B ε τ θ t)/
      (1-preferredSelectedContinuedProduct d B ε τ θ t)‖≤R)
    (hdet : ‖(gaugeKernel (fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i))
      (fun i => preferredSelectedContinuedRoot d B ε τ θ i t)).det‖≤K)
    (hbody : ∀ i,‖oneBody (preferredSelectedContinuedRoot d B ε τ θ i t)‖≤
      A*preferredSelectedOneBodyProfile d ε (θ i)) :
    ‖preferredSelectedContinuedDensity d B ε τ θ t‖≤
      J*R*K*A^N*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) /
        ((N.factorial:ℝ)*(2*Real.pi)^(N-1)) := by
  have hp (i : Fin N) : 0≤preferredSelectedOneBodyProfile d ε (θ i) := by
    unfold preferredSelectedOneBodyProfile
    positivity
  have hb : ‖∏ i,oneBody (preferredSelectedContinuedRoot d B ε τ θ i t)‖≤
      A^N*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ i,A*preferredSelectedOneBodyProfile d ε (θ i) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hbody i)
      _ = _ := by simp [Finset.prod_mul_distrib]
  have hnum := mul_le_mul (mul_le_mul (mul_le_mul hjac hres (norm_nonneg _) hJ)
    hdet (norm_nonneg _) (mul_nonneg hJ hR)) hb (norm_nonneg _)
    (mul_nonneg (mul_nonneg hJ hR) hK)
  unfold preferredSelectedContinuedDensity
  rw [norm_div]
  simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [preferredSelectedContinuedProduct,mul_assoc] using hnum

end
end IsingBulk.Preferred22
