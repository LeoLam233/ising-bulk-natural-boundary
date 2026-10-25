import IsingBulk.Joint.RegularEdges.AngularCoefficient
import IsingBulk.Anisotropic.RegularEdges.TailSummability

/-! # The complete differentiated tail on arbitrary holomorphic curves
Every particle number above the retained-dimension threshold is included. The
majorant is independent of the inward point, and is genuinely summable.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

theorem angularDensity_eq_fullIntegrand {N : ℕ} (hN : 0 < N)
    {b : ℝ} {B S : ℂ → ℂ} {u : ℂ}
    (hu : 0 < u.im) (hBi : 0 < (B u).im) (q : Fin N → ℝ) :
    edgeAngularDensity b B S u q = edgeFullIntegrand b B S u q := by
  have hd : 1-edgeRootProduct b B u q≠0 :=
    one_sub_coordinateProduct_ne_zero hN (fun i => edgeRoot_norm_lt_one hu hBi (q i))
  rw [edgeAngularDensity,edgeAngularWeight_eq_edgeNumerator]
  unfold edgeFullIntegrand
  field_simp [hd]
  ring

theorem angularDensity_wrapAngle {N : ℕ} (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (q : Fin N → ℝ) :
    edgeAngularDensity b B S u (fun i => wrapAngle (q i)) = edgeAngularDensity b B S u q := by
  simp only [edgeAngularDensity,edgeAngularWeight,edgeRootProduct,
    edgeParamRoot_wrapAngle,angularRootPair_wrapAngle]

section Interior
variable {b : ℝ} {B S : ℂ → ℂ} {U : Set ℂ}
variable (hU : IsOpen U) (hBa : AnalyticOnNhd ℂ B U) (hSa : AnalyticOnNhd ℂ S U)
  (hu : ∀ u ∈ U, 0 < u.im) (hBi : ∀ u ∈ U, 0 < (B u).im) (hS : ∀ u ∈ U, S u ≠ 0)
include hU hBa hSa hu hBi hS

/-- The normalized Lebesgue cube is exactly the probability angular measure;
no particle-dependent measure factor is dropped. -/
theorem angularCoefficient_probability_jets (n j : ℕ) {u : ℂ} (huU : u ∈ U) :
    iteratedDeriv j (angularCoefficient n b B S) u =
      ((n+1).factorial:ℂ)⁻¹ * ∫ q : Fin n → ℝ,
        iteratedDeriv j (fun v => edgeFullIntegrand b B S v (centeredFullAngles n q)) u
          ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  rw [angularCoefficient_iteratedDeriv hU hBa hSa hu hBi hS n j huU]
  unfold edgeCoefficientNormalization edgeFullDerivativeIntegral edgeCenteredCube edgeConstrainedJet
  rw [mul_assoc,←edgeAngleMeasure_integral_eq]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hU.mem_nhds huU] with v hv
  rw [← angularDensity_wrapAngle b B S v (shapeExtend q)]
  exact angularDensity_eq_fullIntegrand (by omega) (hu v hv) (hBi v hv) _

end Interior

/-- All differentiated orders above the dimension threshold are controlled by
one summable sequence, uniformly on the actual whole upper-side disk. -/
theorem angularCoefficient_summable_jet_majorants {b : ℝ} {B S : ℂ → ℂ} {U : Set ℂ}
    (hb : |b| < 1) (hB0 : 0 < (B 0).im) (hBa0 : AnalyticAt ℂ B 0)
    (hSa0 : AnalyticAt ℂ S 0) (hS0 : S 0 ≠ 0)
    (hU : IsOpen U) (hBa : AnalyticOnNhd ℂ B U) (hSa : AnalyticOnNhd ℂ S U)
    (hu : ∀ u ∈ U, 0 < u.im) (hBi : ∀ u ∈ U, 0 < (B u).im) (hS : ∀ u ∈ U, S u ≠ 0)
    (j : ℕ) :
    ∃ δ : ℝ, ∃ G : ℕ → ℝ, 0 < δ ∧ Summable G ∧ (∀ k, 0 ≤ G k) ∧
      ∀ u ∈ U, ‖u‖ < δ → ∀ k : ℕ,
        ‖iteratedDeriv j (angularCoefficient (2*j+3+k) b B S) u‖ ≤ G k := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,hbound⟩ :=
    edgeFullIntegrand_integrated_jets_upper hb hB0 hBa0 hSa0 hS0 j
  let G : ℕ → ℝ := fun k => D*((2*j+3+k+1:ℕ):ℝ)^j *
    particleEdgeMajorant r C M (2*j+3+k+1)
  have hsum : Summable G := by
    have hh := (particleEdgeMajorant_polynomial_summable hr hr1 hC hM j).comp_injective
      (i := fun k : ℕ => 2*j+3+k+1) (by intro a b h; dsimp at h; omega)
    simpa only [G,Function.comp_def,mul_assoc] using hh.mul_left D
  refine ⟨δ,G,hδ,hsum,fun k => mul_nonneg (mul_nonneg hD.le (pow_nonneg (Nat.cast_nonneg _) _))
    (particleEdgeMajorant_nonneg hr.le hC.le hM.le _),?_⟩
  intro u huU hud k
  rw [angularCoefficient_probability_jets hU hBa hSa hu hBi hS _ j huU,norm_mul]
  have hf : ‖(((2*j+3+k+1).factorial:ℂ)⁻¹)‖ ≤ 1 := by
    simp only [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (2*j+3+k+1))
  apply (mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans
  simpa only [one_mul,G,mul_assoc,mul_comm,mul_left_comm] using hbound u (hu u huU) hud k

end
end IsingBulk.Joint.RegularEdges
