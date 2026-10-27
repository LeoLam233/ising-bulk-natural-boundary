import IsingBulk.Preferred22.ContourTheorem
import IsingBulk.Preferred22.ContourDensityBridge
import IsingBulk.Preferred22.PhysicalSeedIntegration
import IsingBulk.Preferred22.ZerothSourceBound
import IsingBulk.Preferred22.PhysicalSymmetries

/-! The actual integrated three-population partition after the full closed
contour deformation. The reflection acts on the original constrained Haar
box and retains the complete physical density and Jacobian. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem preferred_deformedAngles_reflect {N : ℕ} (τ : ℝ) (p : ℝ → ℝ)
    (θ : Fin N → ℝ) :
    deformedAngles τ p (fun x => p (-x)) (-θ) = -deformedAngles τ p (fun x => p (-x)) θ := by
  ext i
  simp only [deformedAngles,Pi.neg_apply,Complex.ofReal_neg]
  have hh : balancedShift τ p (fun x => p (-x)) (-θ) i =
      -balancedShift τ p (fun x => p (-x)) θ i := balancedShift_reflection τ p θ i
  rw [hh]
  push_cast
  ring

theorem preferred_contourMatrix_reflect {N : ℕ} (τ : ℝ) (p : ℝ → ℝ)
    (θ : Fin N → ℝ) :
    preferredContourMatrix τ p (fun x => p (-x)) (-θ) =
      preferredContourMatrix τ p (fun x => p (-x)) θ := by
  ext i j
  simp only [preferredContourMatrix,shiftJacobian,Pi.neg_apply,
    neg_neg,deriv_comp_neg]
  congr 1
  congr 1
  split_ifs <;> ring

theorem preferred_deformedDensity_reflect {N : ℕ} (hN : Even N) (τ : ℝ) (p : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p (fun x => p (-x)) θ i)).im) :
    preferredDeformedPhysicalDensity τ p (fun x => p (-x)) s (-θ) =
      preferredDeformedPhysicalDensity τ p (fun x => p (-x)) s θ := by
  let w := deformedAngles τ p (fun x => p (-x)) θ
  let φ := fun i => preferredArccos (temperatureTrace s-Complex.cos (w i))
  have hz (i : Fin N) : physicalRoot (temperatureTrace s-Complex.cos (w i)) =
      Complex.exp (-Complex.I*φ i) := (preferredArccos_physical_upper _ (hW i)).symm
  have hk : halfAngleKernel (-w) φ = -halfAngleKernel w φ := by
    ext i j
    simp only [halfAngleKernel,Pi.neg_apply,Matrix.neg_apply]
    rw [show (-w i- -w j)/2 = -((w i-w j)/2) by ring,Complex.sin_neg,neg_div]
  simp only [preferredDeformedPhysicalDensity,preferred_deformedAngles_reflect,
    Pi.neg_apply,Complex.cos_neg]
  change ((1+∏ i,physicalRoot (temperatureTrace s-Complex.cos (w i)))/
    (1-∏ i,physicalRoot (temperatureTrace s-Complex.cos (w i))) *
    (gaugeKernel (fun i => Complex.exp (Complex.I*(-w i)))
      (fun i => physicalRoot (temperatureTrace s-Complex.cos (w i)))).det *
      ∏ i,oneBody (physicalRoot (temperatureTrace s-Complex.cos (w i)))) =
    ((1+∏ i,physicalRoot (temperatureTrace s-Complex.cos (w i)))/
    (1-∏ i,physicalRoot (temperatureTrace s-Complex.cos (w i))) *
    (gaugeKernel (fun i => Complex.exp (Complex.I*w i))
      (fun i => physicalRoot (temperatureTrace s-Complex.cos (w i)))).det *
      ∏ i,oneBody (physicalRoot (temperatureTrace s-Complex.cos (w i))))
  simp_rw [hz]
  have hk' : halfAngleKernel (fun i => -w i) φ = -halfAngleKernel w φ := hk
  rw [gaugeKernel_det_eq_halfAngleKernel,gaugeKernel_det_eq_halfAngleKernel,hk',
    Matrix.det_neg,Fintype.card_fin,hN.neg_one_pow,one_mul]

/-- Complete normalized final-contour density, before any population weight. -/
def preferredBareContourDensity {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredContourMatrix τ p m θ).det * preferredDeformedPhysicalDensity τ p m s θ /
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

theorem preferredBareContourDensity_eq_seed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredBareContourDensity τ p m s θ =
      2*preferredPhysicalSeed .right τ (fun _ => 0) p m (fun _ => 1) s θ := by
  simp [preferredBareContourDensity,preferredPhysicalSeed,preferredCellWeight,
    preferredLowerWeight,preferredRightWeight,lowerWeight]
  ring

theorem preferredBareContourDensity_continuous {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) :
    Continuous (fun θ : Fin N → ℝ => preferredBareContourDensity τ B.p B.m
      (IsingBulk.Branch.radialParameter d.alpha ε) θ) := by
  simp_rw [preferredBareContourDensity_eq_seed]
  exact continuous_const.mul
    (preferredPhysicalSeed_radial_contDiff hN d B .right hε hτ _ _ contDiff_const contDiff_const).continuous

def preferredFullPopulationWeight {N : ℕ} (η p m : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  fullWeight (η (occupancy p θ)) (η (occupancy m θ))

def preferredUpperPopulationWeight {N : ℕ} (η p m : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  upperWeight (η (occupancy p θ)) (η (occupancy m θ))

def preferredFullPopulationIntegral (n : ℕ) (τ : ℝ) (η p m : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angularBox n,
    (preferredFullPopulationWeight η p m (constrainedAngles θ):ℂ)*
      preferredBareContourDensity τ p m s (constrainedAngles θ)

def preferredLowerPopulationIntegral (n : ℕ) (τ : ℝ) (η p m : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angularBox n,
    (preferredLowerWeight η p m (constrainedAngles θ):ℂ)*
      preferredBareContourDensity τ p m s (constrainedAngles θ)

def preferredUpperPopulationIntegral (n : ℕ) (τ : ℝ) (η p m : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angularBox n,
    (preferredUpperPopulationWeight η p m (constrainedAngles θ):ℂ)*
      preferredBareContourDensity τ p m s (constrainedAngles θ)

theorem preferred_population_weight_sum {N : ℕ} (η p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    preferredFullPopulationWeight η p m θ + preferredLowerWeight η p m θ +
      preferredUpperPopulationWeight η p m θ = 1 := full_partition _ _

theorem preferred_population_weight_reflect {N : ℕ} (η p : ℝ → ℝ) (θ : Fin N → ℝ) :
    preferredLowerWeight η p (fun x => p (-x)) (-θ) =
      preferredUpperPopulationWeight η p (fun x => p (-x)) θ := by
  simp only [preferredLowerWeight,preferredUpperPopulationWeight,occupancy,Pi.neg_apply,neg_neg]
  exact reflected_weights _ _

theorem preferredBareContourDensity_reflect {N : ℕ} (hN : Even N) (τ : ℝ) (p : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p (fun x => p (-x)) θ i)).im) :
    preferredBareContourDensity τ p (fun x => p (-x)) s (-θ) =
      preferredBareContourDensity τ p (fun x => p (-x)) s θ := by
  rw [preferredBareContourDensity,preferred_contourMatrix_reflect,
    preferred_deformedDensity_reflect hN τ p s θ hW]
  rfl

/-- Exact normalization and density bridge from the full homotopy to the
complete physical scalar used by the partition and transport modules. -/
theorem preferred_bare_integral_eq_coefficient (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) :
    (∫ θ in angularBox n, preferredBareContourDensity τ B.p B.m
      (IsingBulk.Branch.radialParameter d.alpha ε) (constrainedAngles θ)) =
        coefficient (n+1) (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hc := (exact_constrained_deformation s (preferredRadialTrace_im_pos d hε) τ hτ
    B.p B.m B.smooth B.m_smooth B.periodic B.m_periodic B.lower_bound
    (fun x => B.lower_bound (-x)) (fun _ hx => B.p_zero_of_sin_nonpos hx)
    (fun _ hx => B.m_zero_of_sin_nonneg hx)).1 n
  rw [hc,deformedCoefficient_density_formula,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    have hM : fullAngularJacobian τ 1 B.p B.m (constrainedAngles θ) =
        preferredContourMatrix τ B.p B.m (constrainedAngles θ) := by
      ext i j
      simp only [fullAngularJacobian,preferredContourMatrix,Complex.ofReal_one,mul_one]
    rw [constrainedAngularJacobian_det_eq_full τ 1 B.p B.m B.smooth B.m_smooth,hM]
    have hD : complexAngularDensity (s,deformedAngles τ B.p B.m (constrainedAngles θ)) =
        preferredDeformedPhysicalDensity τ B.p B.m s (constrainedAngles θ) := by
      simp only [preferredDeformedPhysicalDensity,gaugeKernel_det_normalization]
      rfl
    rw [hD]
    simp only [preferredBareContourDensity,Nat.add_sub_cancel,s]
    ring

theorem preferred_lower_upper_population_equal (n : ℕ) (he : Even (n+1))
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (η : ℝ → ℝ) :
    preferredLowerPopulationIntegral n τ η B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) =
      preferredUpperPopulationIntegral n τ η B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) := by
  unfold preferredLowerPopulationIntegral preferredUpperPopulationIntegral
  rw [← angularBox_integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    rw [constrainedAngles_neg]
    have hW (i : Fin (n+1)) :
        0<(temperatureTrace (IsingBulk.Branch.radialParameter d.alpha ε)-
          Complex.cos (deformedAngles τ B.p B.m (constrainedAngles θ) i)).im := by
      have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
        (by linarith [d.alpha_lt,Real.pi_pos])
      exact (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ (constrainedAngles θ) i)
    change (preferredLowerWeight η B.p (fun x => B.p (-x)) (-(constrainedAngles θ)):ℂ)*
      preferredBareContourDensity τ B.p (fun x => B.p (-x)) _ (-(constrainedAngles θ)) = _
    rw [preferred_population_weight_reflect,
      preferredBareContourDensity_reflect he τ B.p _ _ hW]
    rfl

/-- The literal integrated C_N = F_N + 2 L_N identity, at every positive
radial displacement and every positive even particle order. -/
theorem preferred_complete_population_partition (n : ℕ) (he : Even (n+1))
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (η : ℝ → ℝ) (hη : Continuous η) :
    coefficient (n+1) (IsingBulk.Branch.radialParameter d.alpha ε) =
      preferredFullPopulationIntegral n τ η B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) +
        2*preferredLowerPopulationIntegral n τ η B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let f := fun θ : Fin n → ℝ => preferredBareContourDensity τ B.p B.m s (constrainedAngles θ)
  let F := fun θ : Fin n → ℝ => (preferredFullPopulationWeight η B.p B.m (constrainedAngles θ):ℂ)*f θ
  let L := fun θ : Fin n → ℝ => (preferredLowerWeight η B.p B.m (constrainedAngles θ):ℂ)*f θ
  let U := fun θ : Fin n → ℝ => (preferredUpperPopulationWeight η B.p B.m (constrainedAngles θ):ℂ)*f θ
  have hf : Continuous f := (preferredBareContourDensity_continuous (by omega) d B hε hτ).comp
    (constrainedAngles_continuous n)
  have hp := B.smooth.continuous
  have hm := B.m_smooth.continuous
  have hc := constrainedAngles_continuous n
  have hF : Continuous F := by
    dsimp only [F]
    apply Continuous.mul _ hf
    apply Complex.continuous_ofReal.comp
    unfold preferredFullPopulationWeight fullWeight occupancy
    fun_prop
  have hL : Continuous L := by
    dsimp only [L]
    apply Continuous.mul _ hf
    apply Complex.continuous_ofReal.comp
    unfold preferredLowerWeight lowerWeight occupancy
    fun_prop
  have hU : Continuous U := by
    dsimp only [U]
    apply Continuous.mul _ hf
    apply Complex.continuous_ofReal.comp
    unfold preferredUpperPopulationWeight upperWeight occupancy
    fun_prop
  have hiF := continuous_integrableOn_angularBox hF
  have hiL := continuous_integrableOn_angularBox hL
  have hiU := continuous_integrableOn_angularBox hU
  have hpoint (θ : Fin n → ℝ) : (F θ+L θ)+U θ=f θ := by
    dsimp only [F,L,U]
    rw [← add_mul,← add_mul,← Complex.ofReal_add,← Complex.ofReal_add,
      preferred_population_weight_sum,Complex.ofReal_one,one_mul]
  have hi : (∫ θ in angularBox n,f θ)=
      (∫ θ in angularBox n,F θ)+(∫ θ in angularBox n,L θ)+(∫ θ in angularBox n,U θ) := by
    calc
      _ = ∫ θ in angularBox n,(F θ+L θ)+U θ :=
        integral_congr_ae (Filter.Eventually.of_forall fun θ => (hpoint θ).symm)
      _ = (∫ θ in angularBox n,F θ+L θ)+(∫ θ in angularBox n,U θ) :=
        integral_add (hiF.add hiL) hiU
      _ = _ := congrArg (fun z => z+∫ θ in angularBox n,U θ) (integral_add hiF hiL)
  have hb := preferred_bare_integral_eq_coefficient n d B hε hτ
  change (∫ θ in angularBox n,f θ)=coefficient (n+1) s at hb
  rw [← hb,hi]
  change preferredFullPopulationIntegral n τ η B.p B.m s +
      preferredLowerPopulationIntegral n τ η B.p B.m s +
      preferredUpperPopulationIntegral n τ η B.p B.m s = _
  rw [← preferred_lower_upper_population_equal n he d B hε hτ η]
  ring

end
end IsingBulk.Preferred22
