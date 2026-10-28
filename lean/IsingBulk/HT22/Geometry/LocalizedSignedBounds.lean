import IsingBulk.HT22.Geometry.LocalizedSignedContour

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.Preferred22 IsingBulk.First IsingBulk.Branch LocalLimit
open scoped Topology BigOperators

/-- Source chart radius for every regular right-arc signed equality mean. -/
theorem regular_signed_mean_chart_radius (n : ℕ) (negative : Bool)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (l : ℤ)
    {ρ : ℝ} (hρ : 0<ρ)
    (hmean : signedEqualityMean negative (n+1) l∈Icc (-d.b+ρ) B.delta) :
    ∃ R : ℝ,0<R ∧ ∀ θ : Fin n → ℝ,
      ‖θ-(fun _ => signedEqualityMean negative (n+1) l)‖<R →
      θ∈angularBox n ∧ preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)=
        constrainedAtTotal (Physical.constraintAngle negative+2*Real.pi*(l:ℝ)) θ := by
  have hstrip : signedEqualityMean negative (n+1) l∈Ioo (-Real.pi-B.delta) (-Real.pi-B.delta+2*Real.pi) := by
    constructor <;> linarith [hmean.1,hmean.2,d.b_lt,B.delta_pos,B.delta_alpha,d.alpha_lt,Real.pi_pos]
  have horig : signedEqualityMean negative (n+1) l∈Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [hmean.1,hmean.2,d.b_lt,B.delta_alpha,d.alpha_lt,Real.pi_pos]
  simpa only [signedEqualityMean,add_comm] using signed_equality_chart_radius n B.delta
    (Physical.constraintAngle negative) l
    (by simpa only [signedEqualityMean,add_comm] using hstrip)
    (by simpa only [signedEqualityMean,add_comm] using horig)

/-- Bounded derivatives of a localized piece of the literal original
signed torus integral, including any continuous original-angle weight
(such as the actual contour Jacobian and smooth cutoff). -/
theorem localized_signed_integral_derivatives_bounded (n : ℕ) (negative : Bool)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (l : ℤ) {ρ : ℝ} (hρ : 0<ρ)
    (hmean : signedEqualityMean negative (n+1) l∈Icc (-d.b+ρ) B.delta)
    (β : ℝ) (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos d.alpha-Real.cos (signedEqualityMean negative (n+1) l)=Real.cos β)
    (hgap : 1-Physical.constraintSign negative*(Complex.exp (-(β:ℂ)*Complex.I))^(n+1)≠0) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,Continuous χ →
      (∀ θ,χ θ≠0 → ‖θ-(fun _ => signedEqualityMean negative (n+1) l)‖<R) →
      ∀ W : (Fin (n+1) → ℝ) → ℂ,Continuous W → ∀ j : ℕ,
      ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖(deriv^[j] (localizedSignedLiftedIntegral n negative d B τ χ W)) (radialParameter d.alpha ε)‖≤C := by
  obtain ⟨Ra,hRa,ha⟩ := balanced_signed_local_derivatives_bounded n negative d B hτ
    (signedEqualityMean negative (n+1) l) β hβ hβπ hrel hgap
  obtain ⟨Rb,hRb,hchart⟩ := regular_signed_mean_chart_radius n negative d B l hρ hmean
  refine ⟨min Ra Rb,lt_min hRa hRb,?_⟩
  intro χ hχ hsupp W hW j
  let μ := signedEqualityMean negative (n+1) l
  let χs : (Fin n → ℝ) → ℂ := fun u => χ (fun i => μ+u i)*W (fun i => μ+shapeExtend u i)
  have hshape : Continuous (shapeExtend : (Fin n → ℝ) → (Fin (n+1) → ℝ)) := by
    unfold shapeExtend
    fun_prop
  have hc : Continuous χs := by dsimp [χs]; fun_prop
  have hs (u : Fin n → ℝ) (hu : χs u≠0) : ‖u‖<Ra := by
    have hχu : χ (fun i => μ+u i)≠0 := (mul_ne_zero_iff.mp hu).1
    have hh := (hsupp _ hχu).trans_le (min_le_left _ _)
    have he : (fun i => μ+u i)-(fun _ => μ)=u := by funext i; simp
    change ‖(fun i => μ+u i)-(fun _ => μ)‖<Ra at hh
    simpa only [he] using hh
  have heq : localizedSignedLiftedIntegral n negative d B τ χ W=
      fun t => ∫ u : Fin n → ℝ,χs u*Physical.complexSignedDensity negative
        (t,balancedEqualityChart τ B.p B.m μ u) := by
    funext t
    exact localizedSignedLiftedIntegral_eq_chart n negative d B τ l Rb hchart χ
      (fun θ hθ => (hsupp θ hθ).trans_le (min_le_right _ _)) W t
  rw [heq]
  exact ha χs hc hs j

end
end IsingBulk.HT22.Geometry
