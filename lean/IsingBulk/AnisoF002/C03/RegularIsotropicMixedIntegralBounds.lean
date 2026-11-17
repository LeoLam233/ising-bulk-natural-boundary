import IsingBulk.AnisoF002.C03.RegularIsotropicMixedCoefficient
import IsingBulk.AnisoF002.C03.RegularIsotropicBoxProducts
import IsingBulk.AnisoF002.C03.IsotropicActualDeterminantBound

/-!
# Full mixed coefficient bounds on the original constrained measure

Every derivative is integrated with all factors present. The first N-1
one-body factors use their genuine L1 envelope; the last constrained
factor uses the constructed O(N) gap. This harmless polynomial loss is
kept explicitly.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

def mixedIntegratedEnvelope (C g c ρ L : ℝ) (j N : ℕ) : ℝ :=
  2 ^ N * ((j.factorial : ℝ) * mixedDensityEnvelope C g N / (ρ / (N : ℝ) ^ 6) ^ j) *
    (2 * N / c) * L ^ (N - 1)

theorem mixedDensityEnvelope_nonneg {C g : ℝ} (hC : 0 ≤ C) (hg : 0 < g) (N : ℕ) :
    0 ≤ mixedDensityEnvelope C g N := by
  unfold mixedDensityEnvelope
  positivity

namespace ActualMixedRootControl
variable {α b η τ δ : ℝ} (d : ActualMixedRootControl α b η τ δ)

theorem actual_oneBody_particle_bound {N : ℕ} (hN : 0 < N)
    (hα : 0 < α ∧ α < Real.pi) (hδ1 : δ ≤ 1) (hη : 0 < η) (hτ : 0 ≤ τ)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    (i : Fin N) :
    ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) /
      (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) ^ 2)‖ ≤
      2 * N / d.pairGap := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hSi := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hri : ‖isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i)‖ ≤ 1 :=
    upperEdgeRoot_norm_le_one (Or.inl
    (actual_balanced_homotopy_sheet _ hSi η τ 1 hη hτ zero_le_one θ i))
  have hgap := d.center_gap N hN ε hε hεδ θ hP hQ i i
  rw [← pow_two] at hgap
  rw [norm_div, norm_mul, Complex.norm_two]
  apply (div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
    (by linarith : 2 * ‖isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i)‖ ≤ 2)
    (div_pos d.pairGap_pos hN0) hgap).trans_eq
  field_simp

theorem actualBodyNormProduct_constrained_bound (n : ℕ)
    (hα : 0 < α ∧ α < Real.pi) (hδ1 : δ ≤ 1) (hη : 0 < η) (hτ : 0 ≤ τ)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (a : ℝ) (x : Fin n → ℝ)
    (hx : x ∈ angularIntegrationBox n)
    (hP : 1 / 4 ≤ actualUpperPopulation η (affineConstraintAngles a x))
    (hQ : 1 / 4 ≤ actualLowerPopulation η (affineConstraintAngles a x))
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hbody : ∀ (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)), θ i ∈ Icc 0 (2 * Real.pi) →
      ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) /
        (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) ^ 2)‖ ≤ f (θ i)) :
    actualBodyNormProduct (isotropicRadialParameter α ε) η τ (affineConstraintAngles a x) ≤
      (2 * (n + 1 : ℕ) / d.pairGap) * ∏ i, f (x i) := by
  have hfirst (i : Fin n) : affineConstraintAngles a x i.castSucc = x i := by
    rw [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc]
  have hfi (i : Fin n) := hbody (affineConstraintAngles a x) i.castSucc
    (by rw [hfirst]; exact ⟨hx.1 i, hx.2 i⟩)
  simp only [hfirst] at hfi
  have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => norm_nonneg _) (fun i _ => hfi i)
  have hl := d.actual_oneBody_particle_bound (by omega : 0 < n + 1) hα hδ1 hη hτ hε hεδ
    (affineConstraintAngles a x) hP hQ (Fin.last n)
  unfold actualBodyNormProduct
  rw [Fin.prod_univ_castSucc]
  have hh := mul_le_mul hp hl (norm_nonneg _) (Finset.prod_nonneg (fun i _ => hf (x i)))
  exact hh.trans_eq (mul_comm _ _)

theorem mixed_integrand_jet_bound (n : ℕ)
    (hα : 0 < α ∧ α < Real.pi) (hδ1 : δ ≤ 1) (hη : 0 < η) (hτ : 0 ≤ τ)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (a : ℝ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1)
    (hdet : ∀ θ : Fin (n + 1) → ℝ, ‖(actualBalancedJacobian η τ 1 θ).det‖ ≤ 2 ^ (n + 1))
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hbody : ∀ (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)), θ i ∈ Icc 0 (2 * Real.pi) →
      ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) /
        (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) ^ 2)‖ ≤ f (θ i))
    (j : ℕ) (x : Fin n → ℝ) (hx : x ∈ angularIntegrationBox n) :
    ‖iteratedDeriv j (fun S => mixedPhysicalIntegrand η τ σ S (affineConstraintAngles a x))
      (isotropicRadialParameter α ε)‖ ≤
      (2 ^ (n + 1) * ((j.factorial : ℝ) * mixedDensityEnvelope d.pairConstant d.productGap (n + 1) /
        (d.radius / (n + 1 : ℕ) ^ 6) ^ j) * (2 * (n + 1 : ℕ) / d.pairGap)) * ∏ i, f (x i) := by
  let θ := affineConstraintAngles a x
  let K := (j.factorial : ℝ) * mixedDensityEnvelope d.pairConstant d.productGap (n + 1) /
    (d.radius / (n + 1 : ℕ) ^ 6) ^ j
  have hK : 0 ≤ K := by
    have he := mixedDensityEnvelope_nonneg (zero_le_one.trans d.pairConstant_ge_one) d.productGap_pos (n + 1)
    dsimp [K]
    positivity [d.radius_pos]
  have hfprod : 0 ≤ ∏ i, f (x i) := Finset.prod_nonneg (fun i _ => hf (x i))
  change ‖iteratedDeriv j (fun S => mixedAngularAmplitude η τ θ *
    isotropicBarePhysicalDensity S σ (actualHomotopyAngle η τ 1 θ)) (isotropicRadialParameter α ε)‖ ≤
      (2 ^ (n + 1) * K * (2 * (n + 1 : ℕ) / d.pairGap)) * ∏ i, f (x i)
  rw [iteratedDeriv_const_mul_field, norm_mul]
  by_cases hcut : mixedPopulationCutoff η θ = 0
  · have hz : mixedAngularAmplitude η τ θ = 0 := by
      simp only [mixedAngularAmplitude, hcut, Complex.ofReal_zero, zero_mul]
    rw [hz, norm_zero, zero_mul]
    positivity [d.pairGap_pos]
  · obtain ⟨hP, hQ⟩ := mixedPopulationCutoff_support η θ hcut
    have hj := d.physical_density_jet_bound (by omega : 0 < n + 1) hα hδ1 hη hτ hε hεδ θ hP.le hQ.le hσ j
    have he := congrFun (iteratedDeriv_comp_const_add
      (f := fun T => isotropicBarePhysicalDensity T σ (actualHomotopyAngle η τ 1 θ))
      (s := isotropicRadialParameter α ε) (n := j)) (0 : ℂ)
    simp only [add_zero] at he
    rw [he] at hj
    have hb := d.actualBodyNormProduct_constrained_bound n hα hδ1 hη hτ hε hεδ a x hx hP.le hQ.le f hf hbody
    have hA : ‖mixedAngularAmplitude η τ θ‖ ≤ 2 ^ (n + 1) := by
      rw [mixedAngularAmplitude, norm_mul, Complex.norm_real, Real.norm_of_nonneg (actual_population_partition_bounds η θ).1.1]
      exact (mul_le_mul (actual_population_partition_bounds η θ).1.2 (hdet θ) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have h1 := hj.trans (mul_le_mul_of_nonneg_left hb hK)
    have h2 := mul_le_mul hA h1 (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
    apply h2.trans_eq
    ring

theorem coefficient_jet_integral_bound (n : ℕ)
    (hα : 0 < α ∧ α < Real.pi) (hδ1 : δ ≤ 1) (hη : 0 < η) (hτ : 0 ≤ τ)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (a : ℝ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1)
    (hdet : ∀ θ : Fin (n + 1) → ℝ, ‖(actualBalancedJacobian η τ 1 θ).det‖ ≤ 2 ^ (n + 1))
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hfI : IntegrableOn f (Icc 0 (2 * Real.pi)) volume) {L : ℝ}
    (hL : (∫ t in Icc 0 (2 * Real.pi), f t) ≤ L)
    (hbody : ∀ (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)), θ i ∈ Icc 0 (2 * Real.pi) →
      ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) /
        (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) ^ 2)‖ ≤ f (θ i))
    (j : ℕ) :
    ‖iteratedDeriv j (mixedPhysicalCoefficient n η τ a σ) (isotropicRadialParameter α ε)‖ ≤
      mixedIntegratedEnvelope d.pairConstant d.productGap d.pairGap d.radius L j (n + 1) := by
  have hSi := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  rw [mixedPhysicalCoefficient_iteratedDeriv n hη hτ a hSi hσ j]
  let M := 2 ^ (n + 1) * ((j.factorial : ℝ) * mixedDensityEnvelope d.pairConstant d.productGap (n + 1) /
    (d.radius / (n + 1 : ℕ) ^ 6) ^ j) * (2 * (n + 1 : ℕ) / d.pairGap)
  have hM : 0 ≤ M := by
    have he := mixedDensityEnvelope_nonneg (zero_le_one.trans d.pairConstant_ge_one) d.productGap_pos (n + 1)
    dsimp [M]
    positivity [d.pairGap_pos, d.radius_pos]
  have hprodI := angularIntegrationBox_product_integrable n hfI
  have hjetI := mixedPhysicalCoefficient_jets_integrable n hη hτ a hSi hσ j
  calc
    _ ≤ ∫ x in angularIntegrationBox n,
        ‖iteratedDeriv j (fun S => mixedPhysicalIntegrand η τ σ S (affineConstraintAngles a x))
          (isotropicRadialParameter α ε)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in angularIntegrationBox n, M * ∏ i, f (x i) := by
      apply integral_mono_ae hjetI.norm (hprodI.const_mul M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact d.mixed_integrand_jet_bound n hα hδ1 hη hτ hε hεδ a hσ hdet f hf hbody j x hx
    _ = M * ∫ x in angularIntegrationBox n, ∏ i, f (x i) := integral_const_mul _ _
    _ ≤ M * L ^ n := mul_le_mul_of_nonneg_left (angularIntegrationBox_product_integral_bound n hf hL) hM
    _ = _ := by simp only [mixedIntegratedEnvelope, Nat.add_sub_cancel]; rfl

end ActualMixedRootControl
end
end IsingBulk.AnisoF002.Isotropic
