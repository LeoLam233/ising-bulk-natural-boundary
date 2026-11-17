import IsingBulk.AnisoF002.C03.IsotropicHomotopyPeriodicity

/-!
# The actual balanced contour deformation preserves its constrained integral

This theorem differentiates the literal finite real angular integral,
uses the constructed tangent current, and cancels the exactly periodic
opposite faces. The homotopy determinant is the complete full Jacobian.
The common deformation size is chosen before every particle number.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter MeasureTheory

abbrev angularIntegrationBox (n : ℕ) : Set (Fin n → ℝ) :=
  Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi)

def balancedConstrainedIntegral {n : ℕ} (η τ a : ℝ)
    (F : (Fin (n + 1) → ℂ) → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x in angularIntegrationBox n,
    homotopyPulledDensity η τ F (ξ, affineConstraintAngles a x)

theorem insertNth_period_face {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) :
    (i.insertNth (2 * Real.pi) y : Fin (n + 1) → ℝ) =
      (i.insertNth 0 y : Fin (n + 1) → ℝ) + Pi.single i (2 * Real.pi) := by
  funext j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp
  · simp

theorem balancedConstrainedIntegral_hasDerivAt_zero {n : ℕ} (η τ a ξ : ℝ)
    (F : (Fin (n + 2) → ℂ) → ℂ) (hp : AngularPeriodic F)
    (hF : ∀ θ : Fin (n + 2) → ℝ, AnalyticAt ℂ F (actualHomotopyAngle η τ ξ θ))
    (hdet : ∀ θ : Fin (n + 2) → ℝ, (actualBalancedJacobian η τ ξ θ).det ≠ 0) :
    HasDerivAt (balancedConstrainedIntegral η τ a F) 0 ξ := by
  let K := angularIntegrationBox (n + 1)
  let f : ℝ × (Fin (n + 2) → ℝ) → ℂ := homotopyPulledDensity η τ F
  let g : (Fin (n + 1) → ℝ) → (Fin (n + 2) → ℝ) := affineConstraintAngles a
  let P : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ :=
    fun i x => homotopyCurrentFlux η τ F i.castSucc (ξ, g x)
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hg : Continuous g := (affineConstraintAngles_contDiff a 1).continuous
  have hf (x : Fin (n + 1) → ℝ) : ContDiffAt ℝ 1 f (ξ, g x) :=
    (homotopyPulledDensity_contDiffAt η τ F (ξ, g x) (hF (g x))).of_le (by simp)
  obtain ⟨hI, hD⟩ := integral_hasDerivAt_of_joint_C1 (μ := volume.restrict K)
    (f := f) (g := g) hK (ae_restrict_mem measurableSet_Icc) hg (fun x _ => hf x)
  have hP (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : DifferentiableAt ℝ (P i) x := by
    change DifferentiableAt ℝ (fun y => homotopyCurrentFlux η τ F i.castSucc
      (ξ, affineConstraintAngles a y)) x
    exact ((homotopyCurrentFlux_contDiffAt η τ F (ξ, g x) (hF (g x))
      (hdet (g x)) i.castSucc).differentiableAt (by simp)).comp x
        ((differentiableAt_const ξ).prodMk ((affineConstraintAngles_contDiff a 1).differentiable_one x))
  have he (x : Fin (n + 1) → ℝ) :
      (∑ i, fderiv ℝ (P i) x (Pi.single i 1)) = realParameterPartial f (ξ, g x) := by
    have hh := actual_homotopy_affine_current η τ a ξ F x (hF (g x)) (hdet (g x))
    have hd := realParameterPartial_hasDerivAt (hf x)
    change (∑ i, scalarPartial (P i) (Pi.single i 1) x) = _
    rw [← hh, hd.deriv]
  have hz : (∫ x in K, realParameterPartial f (ξ, g x)) = 0 := by
    have hdiv : IntegrableOn (fun x => ∑ i, fderiv ℝ (P i) x (Pi.single i 1)) K volume := by
      change Integrable (fun x => ∑ i, fderiv ℝ (P i) x (Pi.single i 1)) (volume.restrict K)
      simpa only [he] using hI
    have hzero := periodic_box_divergence_zero (0 : Fin (n + 1) → ℝ)
      (fun _ => 2 * Real.pi) (fun _ => by positivity) P
      (fun i x => fderiv ℝ (P i) x) ∅ countable_empty
      (fun i x _ => (hP i x).continuousAt.continuousWithinAt)
      (fun x _ i => (hP i x).hasFDerivAt) hdiv
      (fun i y _ => by
        change homotopyCurrentFlux η τ F i.castSucc
          (ξ, affineConstraintAngles a (i.insertNth (2 * Real.pi) y)) = _
        rw [insertNth_period_face, constrained_homotopy_flux_periodic η τ a ξ F hp]
        rfl)
    simpa only [he] using hzero
  rw [hz] at hD
  exact hD

/-- Genuine full-Jacobian constrained deformation, including all times
and all particle numbers N >= 2. Analyticity is needed only on the
actual deformed image, and will be discharged for the physical density. -/
theorem exists_balanced_constrained_integral_invariance (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ), ∀ τ ∈ Icc 0 δ, ∀ a : ℝ,
      ∀ F : (Fin (n + 2) → ℂ) → ℂ, AngularPeriodic F →
      (∀ ξ ∈ Icc 0 1, ∀ θ : Fin (n + 2) → ℝ,
        AnalyticAt ℂ F (actualHomotopyAngle η τ ξ θ)) →
      balancedConstrainedIntegral η τ a F 1 = balancedConstrainedIntegral η τ a F 0 := by
  obtain ⟨δ, hδ, hregular⟩ := exists_actual_homotopy_invertible η
  refine ⟨δ, hδ, ?_⟩
  intro n τ hτ a F hp hF
  have hd (ξ : ℝ) (hξ : ξ ∈ Icc 0 1) :
      HasDerivAt (balancedConstrainedIntegral η τ a F) 0 ξ :=
    balancedConstrainedIntegral_hasDerivAt_zero η τ a ξ F hp (hF ξ hξ)
      (hregular (n + 2) (by omega) τ hτ ξ hξ)
  have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun ξ hξ => (hd ξ hξ).differentiableAt)
    (fun ξ hξ => by rw [(hd ξ hξ).deriv, norm_zero])
    (convex_Icc (0 : ℝ) 1) (show 0 ∈ Icc (0 : ℝ) 1 by simp)
    (show 1 ∈ Icc (0 : ℝ) 1 by simp)
  have hzero : balancedConstrainedIntegral η τ a F 1 - balancedConstrainedIntegral η τ a F 0 = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _))
  exact sub_eq_zero.mp hzero

end IsingBulk.AnisoF002.Isotropic
