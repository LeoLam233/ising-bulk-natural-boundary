import IsingBulk.AnisoF002.C03.IsotropicCurrentOutsideSupport
import IsingBulk.AnisoF002.C03.IsotropicCenteredCurrentCalculus

/-!
# Continuous actual constrained flux across total coincidence

Retained collision powers give a continuous zero value at the single
centered coincidence. Every other value and derivative is unchanged.
The actual compact angular cutoff also makes every outer box face
identically zero, so the checked divergence theorem has no boundary
term and no unproved differentiability premise at coincidence.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators Classical

theorem actual_centered_flux_continuous_extension {n : ℕ}
    (α b β ρ ε e : ℝ) (η τ ξ : ℝ) (σ c : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (j : ℕ) (k : Fin (n + 1)) (C : ℝ) (p : ℕ)
    (hε : 0 < ε) (he : 0 < e) (heε : e ≤ ε) (hC : 0 ≤ C) (hp : 1 ≤ p)
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β)
    (hreg : ∀ θ : Fin (n + 1) → ℝ, (∀ i, θ i ∈ Icc (-b - β) β) →
      (∃ i l, θ i ≠ θ l) → DifferentiableAt ℝ (actualTransportedFlux σ η τ ξ g j k)
        (isotropicRadialParameter α ε, θ))
    (hbound : ∀ θ : Fin (n + 1) → ℝ, (∀ i, θ i ∈ Icc (-b - β) β) →
      ∀ t : ℝ, 0 < t → (∀ i l, |θ i - θ l| ≤ 2 * t) → (∃ i l, t ≤ |θ i - θ l|) →
      ‖actualTransportedFlux σ η τ ξ g j k (isotropicRadialParameter α ε, θ)‖ ≤
        C * (isotropicShellDelta b ε t θ) ^ p) :
    let f := fun x : Fin n → ℝ => c * actualTransportedFlux σ η τ ξ g j k
      (isotropicRadialParameter α ε, centeredConstraintAngles ρ x)
    Continuous (zeroAtCoincidence f) ∧
      ∀ x : Fin n → ℝ, x ≠ 0 → HasFDerivAt (zeroAtCoincidence f) (fderiv ℝ f x) x := by
  dsimp only
  let f := fun x : Fin n → ℝ => c * actualTransportedFlux σ η τ ξ g j k
    (isotropicRadialParameter α ε, centeredConstraintAngles ρ x)
  have hf (x : Fin n → ℝ) (hx : x ≠ 0) : DifferentiableAt ℝ f x := by
    have hfull : DifferentiableAt ℝ (actualTransportedFlux σ η τ ξ g j k)
        (isotropicRadialParameter α ε, centeredConstraintAngles ρ x) := by
      by_cases hs : centeredConstraintAngles ρ x ∈ tsupport g
      · exact hreg _ (hsupport _ hs) (centeredConstraintAngles_nonconstant ρ x hx)
      · exact (actualTransportedFlux_outside_smooth σ η τ ξ g j k _ hs).differentiableAt (by simp)
    exact ((hfull.comp x (centered_joint_hasFDerivAt _ ρ x).differentiableAt).const_mul c)
  let L := 2 * ‖constrainedTangentMap n‖ / Real.sqrt e
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hestimate (x : Fin n → ℝ) (hx : x ≠ 0) : ‖f x‖ ≤ (‖c‖ * C * L ^ p) * ‖x‖ ^ p := by
    by_cases hs : centeredConstraintAngles ρ x ∈ tsupport g
    · obtain ⟨t, ht, hd, hl, hscale⟩ := centered_actual_shell_scale_witness ρ b ε e he heε x hx
      have hh := hbound _ (hsupport _ hs) t ht hd hl
      have hΔ : 0 ≤ isotropicShellDelta b ε t (centeredConstraintAngles ρ x) :=
        (isotropicShellDelta_pos b ε t _ hε ht).le
      change ‖c * actualTransportedFlux σ η τ ξ g j k _‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ ‖c‖ * (C * (isotropicShellDelta b ε t (centeredConstraintAngles ρ x)) ^ p) := by gcongr
        _ ≤ ‖c‖ * (C * (L * ‖x‖) ^ p) := by gcongr
        _ = _ := by rw [mul_pow]; ring
    · have hz := (actualTransportedFlux_zero_germ σ η τ ξ g j k
        (isotropicRadialParameter α ε, centeredConstraintAngles ρ x) hs).eq_of_nhds
      change ‖c * actualTransportedFlux σ η τ ξ g j k _‖ ≤ _
      rw [hz, mul_zero, norm_zero]
      positivity
  refine ⟨zeroAtCoincidence_continuous f (‖c‖ * C * L ^ p) 1 p (by positivity) zero_lt_one hp
    (fun x hx => (hf x hx).continuousAt) (fun x _ hx => hestimate x hx), ?_⟩
  intro x hx
  exact (hf x hx).hasFDerivAt.congr_of_eventuallyEq (zeroAtCoincidence_germ hx)

theorem centered_flux_extension_zero_off_box {n : ℕ} (L U ρ : ℝ) (s σ c : ℂ)
    (η τ ξ : ℝ) (g : (Fin (n + 1) → ℝ) → ℂ) (j : ℕ) (k : Fin (n + 1))
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc L U)
    (x : Fin n → ℝ) (hx : x ∉ Icc (fun _ => L - ρ) (fun _ => U - ρ)) :
    zeroAtCoincidence (fun y => c * actualTransportedFlux σ η τ ξ g j k
      (s, centeredConstraintAngles ρ y)) x = 0 := by
  by_cases hx0 : x = 0
  · subst x
    exact zeroAtCoincidence_zero _
  · rw [zeroAtCoincidence, ite_eq_right hx0,
      centered_transport_flux_zero_off_box L U ρ s σ η τ ξ g j k hsupport x hx, mul_zero]

theorem centered_flux_extension_outer_faces {n : ℕ} (L U ρ : ℝ) (s σ c : ℂ)
    (η τ ξ : ℝ) (g : (Fin (n + 2) → ℝ) → ℂ) (j : ℕ) (k : Fin (n + 2))
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc L U)
    (i : Fin (n + 1)) (y : Fin n → ℝ) :
    zeroAtCoincidence (fun x => c * actualTransportedFlux σ η τ ξ g j k
      (s, centeredConstraintAngles ρ x)) (i.insertNth (U - ρ + 1) y) = 0 ∧
    zeroAtCoincidence (fun x => c * actualTransportedFlux σ η τ ξ g j k
      (s, centeredConstraintAngles ρ x)) (i.insertNth (L - ρ - 1) y) = 0 := by
  constructor
  · apply centered_flux_extension_zero_off_box L U ρ s σ c η τ ξ g j k hsupport
    intro hx
    have hh := hx.2 i
    simp only [Fin.insertNth_apply_same] at hh
    linarith
  · apply centered_flux_extension_zero_off_box L U ρ s σ c η τ ξ g j k hsupport
    intro hx
    have hh := hx.1 i
    simp only [Fin.insertNth_apply_same] at hh
    linarith

end
end IsingBulk.AnisoF002.Isotropic
