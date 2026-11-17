import IsingBulk.AnisoF002.C03.IsotropicCurrentRadialData
import IsingBulk.AnisoF002.C03.IsotropicFluxZeroExtension
import IsingBulk.AnisoF002.C03.IsotropicExceptionalCurrentIntegral

/-!
# The complete physical right current integrated on the original cycle

This is a genuine differentiation-under-integral theorem for the full
factorial/angular-normalized transported physical density. Its actual
flux has a continuous zero value at total coincidence, every other
derivative is unchanged, and every outer face vanishes by the original
compact angular support. All analytic, geometric, measure and first-jet
conditions are discharged on one fixed positive radial neighborhood.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators ContDiff

structure ActualCurrentInteriorState {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (A : ℝ) : Prop where
  smooth : ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g j) q
  next_smooth : ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g (j + 1)) q
  analytic : AnalyticAt ℂ (fun s => actualTransportedDensity σ η τ ξ g j (s, q.2)) q.1
  flux : ∀ k, DifferentiableAt ℝ (actualTransportedFlux σ η τ ξ g j k) q
  current : ∀ anchor : Fin N,
    scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection q -
      (∑ k ∈ Finset.univ.erase anchor, scalarPartial (actualTransportedFlux σ η τ ξ g j k)
        (actualAngularDirection k - actualAngularDirection anchor) q) =
      actualTransportedDensity σ η τ ξ g (j + 1) q
  value_bound : ‖actualTransportedDensity σ η τ ξ g j q‖ ≤ A
  next_bound : ‖actualTransportedDensity σ η τ ξ g (j + 1) q‖ ≤ A
  derivative_bound : ‖fderiv ℝ (actualTransportedDensity σ η τ ξ g j) q‖ ≤ A

theorem actualCurrentInteriorState_outside {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (A : ℝ)
    (hA : 0 ≤ A) (hq : q.2 ∉ tsupport g) :
    ActualCurrentInteriorState σ η τ ξ g j q A := by
  obtain ⟨hs, ha⟩ := actualTransportedDensity_outside_smooth σ η τ ξ g j q hq
  have hn := actualTransportedDensity_zero_germ σ η τ ξ g (j + 1) q hq
  have hz := actualTransportedDensity_zero_germ σ η τ ξ g j q hq
  refine ⟨hs, (actualTransportedDensity_outside_smooth σ η τ ξ g (j + 1) q hq).1, ha,
    fun k => (actualTransportedFlux_outside_smooth σ η τ ξ g j k q hq).differentiableAt (by simp),
    actualTransportedCurrent_outside σ η τ ξ g j q hq, ?_, ?_, ?_⟩
  · rw [hz.eq_of_nhds, norm_zero]
    exact hA
  · rw [hn.eq_of_nhds, norm_zero]
    exact hA
  · rw [hz.fderiv_eq, fderiv_const_apply, norm_zero]
    exact hA

theorem integrableOn_box_off_zero_bound {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (A : ℝ)
    (hf : ContinuousOn f (Icc a b \ {0}))
    (hb : ∀ x ∈ Icc a b \ {0}, ‖f x‖ ≤ A) :
    IntegrableOn f (Icc a b) volume := by
  let μ : Measure (Fin (n + 1) → ℝ) := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hμ : ∀ᵐ x ∂μ, x ∈ Icc a b \ ({0} : Set (Fin (n + 1) → ℝ)) :=
    (ae_restrict_mem measurableSet_Icc).and ((Set.countable_singleton (0 : Fin (n + 1) → ℝ)).ae_notMem μ)
  have hm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_continuousOn_ae_set
    (measurableSet_Icc.diff (measurableSet_singleton _)) hμ hf
  exact (integrable_const A).mono' hm (hμ.mono fun x hx => hb x hx)

theorem exists_actual_integrated_right_current_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (n : ℕ) (R : Finset (Fin (n + 2) × Fin (n + 2))), R ⊆ indexPairs (n + 2) →
      ∀ j : ℕ, 2 * j + 2 ≤ 2 * R.card →
      ∀ (g : (Fin (n + 2) → ℝ) → ℂ) (Cg : ℝ), 0 ≤ Cg → ContDiff ℝ ∞ g →
        FiniteJetControl (j + 1) g Cg →
        (∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ ρ : ℝ, ∀ ε₀ ∈ Ioo 0 δ,
      Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j
        (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ x)) volume ∧
      Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g (j + 1)
        (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ x)) volume ∧
      HasDerivAt (fun ε : ℝ => ∫ x : Fin (n + 1) → ℝ,
        actualTransportedDensity σ η τ ξ g j (isotropicRadialParameter α ε, centeredConstraintAngles ρ x))
        (isotropicRadialDerivative α ε₀ * ∫ x : Fin (n + 1) → ℝ,
          actualTransportedDensity σ η τ ξ g (j + 1)
            (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ x)) ε₀ := by
  obtain ⟨β, hβ, hβ1, hall⟩ := exists_actual_interior_current_data α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, hδ, hdβ, hdata⟩ := hall η hη hwidth
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro n R hR j hj g Cg hCg hg hgj hsupport σ hσ τ hτ ξ hξ ρ ε₀ hε₀
  obtain ⟨r, A, C, hr, hA, hC, hwindow, hpointdata⟩ :=
    hdata (n + 2) (by omega) R hR j hj g Cg hCg hg hgj σ hσ τ hτ ξ hξ ε₀ hε₀
  let a : Fin (n + 1) → ℝ := fun _ => -b - β - ρ - 1
  let z : Fin (n + 1) → ℝ := fun _ => β - ρ + 1
  have haz : a ≤ z := fun _ => by dsimp [a, z]; linarith
  let D : ℝ → (Fin (n + 1) → ℝ) → ℂ := fun ε x => actualTransportedDensity σ η τ ξ g j
    (isotropicRadialParameter α ε, centeredConstraintAngles ρ x)
  let Dnext : (Fin (n + 1) → ℝ) → ℂ := fun x => actualTransportedDensity σ η τ ξ g (j + 1)
    (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ x)
  let D' : ℝ → (Fin (n + 1) → ℝ) → ℂ := fun ε x => isotropicRadialDerivative α ε *
    scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection
      (isotropicRadialParameter α ε, centeredConstraintAngles ρ x)
  let f : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ := fun i x =>
    isotropicRadialDerivative α ε₀ * actualTransportedFlux σ η τ ξ g j i.castSucc
      (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ x)
  let F := fun i => zeroAtCoincidence (f i)
  let F' := fun i x => fderiv ℝ (f i) x
  have hstate (ε : ℝ) (he : ε ∈ ball ε₀ r) (x : Fin (n + 1) → ℝ) (hx : x ≠ 0) :
      ActualCurrentInteriorState σ η τ ξ g j
        (isotropicRadialParameter α ε, centeredConstraintAngles ρ x) A := by
    by_cases hs : centeredConstraintAngles ρ x ∈ tsupport g
    · obtain ⟨hs₀, hs₁, ha, hf, hc, hv₀, hv₁, hd, _⟩ := hpointdata ε he _
        (hsupport _ hs) (centeredConstraintAngles_nonconstant ρ x hx)
      exact ⟨hs₀, hs₁, ha, hf, hc, hv₀, hv₁, hd⟩
    · exact actualCurrentInteriorState_outside σ η τ ξ g j _ A hA.le hs
  have hD (ε : ℝ) (he : ε ∈ ball ε₀ r) : ContinuousOn (D ε) (Icc a z \ {0}) := by
    intro x hx
    exact ((hstate ε he x (by simpa only [mem_singleton_iff] using hx.2)).smooth.continuousAt.comp
      (f := fun y : Fin (n + 1) → ℝ => (isotropicRadialParameter α ε, centeredConstraintAngles ρ y))
      (centered_joint_hasFDerivAt _ ρ x).continuousAt).continuousWithinAt
  have hDnext : ContinuousOn Dnext (Icc a z \ {0}) := by
    intro x hx
    exact ((hstate ε₀ (mem_ball_self hr) x (by simpa only [mem_singleton_iff] using hx.2)).next_smooth.continuousAt.comp
      (f := fun y : Fin (n + 1) → ℝ => (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ y))
      (centered_joint_hasFDerivAt _ ρ x).continuousAt).continuousWithinAt
  have hD' : ContinuousOn (D' ε₀) (Icc a z \ {0}) := by
    intro x hx
    have hs := (hstate ε₀ (mem_ball_self hr) x (by simpa only [mem_singleton_iff] using hx.2)).smooth
    exact ((scalarPartial_contDiffAt _ actualTimeDirection _ hs).continuousAt.comp
      (f := fun y : Fin (n + 1) → ℝ => (isotropicRadialParameter α ε₀, centeredConstraintAngles ρ y))
      (centered_joint_hasFDerivAt _ ρ x).continuousAt).const_mul _ |>.continuousWithinAt
  have htimeNorm : ‖(actualTimeDirection : ℂ × (Fin (n + 2) → ℝ))‖ = 1 := by
    simp [actualTimeDirection, Prod.norm_def]
  have hD'bound (x : Fin (n + 1) → ℝ) (hx : x ∈ Icc a z \ {0})
      (ε : ℝ) (he : ε ∈ ball ε₀ r) : ‖D' ε x‖ ≤ 2 * A := by
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
    have hs := hstate ε he x hx0
    have hpartial : ‖scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection
        (isotropicRadialParameter α ε, centeredConstraintAngles ρ x)‖ ≤ A := by
      exact ((fderiv ℝ _ _).le_opNorm _).trans (by
        rw [htimeNorm, mul_one]
        exact hs.derivative_bound)
    change ‖isotropicRadialDerivative α ε * _‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (isotropicRadialDerivative_norm_le α ε (hwindow ε he).2.1)
      hpartial (norm_nonneg _) (by norm_num)
  have hDderiv (x : Fin (n + 1) → ℝ) (hx : x ∈ Icc a z \ {0})
      (ε : ℝ) (he : ε ∈ ball ε₀ r) : HasDerivAt (fun u => D u x) (D' ε x) ε := by
    have hs := hstate ε he x (by simpa only [mem_singleton_iff] using hx.2)
    exact radial_hasDerivAt_scalarPartial _ _ (isotropicRadialParameter α) ε _
      (isotropicRadialParameter_hasDerivAt α ε (hwindow ε he).2.1)
      (hs.smooth.differentiableAt (by simp)) hs.analytic.differentiableAt
  have hF (i : Fin (n + 1)) : Continuous (F i) ∧
      ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → HasFDerivAt (F i) (F' i x) x := by
    apply actual_centered_flux_continuous_extension α b β ρ ε₀ (ε₀ / 2) η τ ξ σ
      (isotropicRadialDerivative α ε₀) g j i.castSucc C (2 * R.card - 2 * j - 1)
      hε₀.1 (half_pos hε₀.1) (by linarith [hε₀.1]) hC.le (by omega) hsupport
    · intro θ hθ hne
      exact (hpointdata ε₀ (mem_ball_self hr) θ hθ hne).2.2.2.1 i.castSucc
    · intro θ hθ t ht hdiam hlow
      have hne : ∃ k l, θ k ≠ θ l := by
        obtain ⟨k, l, hkl⟩ := hlow
        exact ⟨k, l, sub_ne_zero.mp (abs_pos.mp (ht.trans_le hkl))⟩
      exact (hpointdata ε₀ (mem_ball_self hr) θ hθ hne).2.2.2.2.2.2.2.2 t ht hdiam hlow i.castSucc
  have hzero : ∀ x ∈ Icc a z \ {0}, ‖D ε₀ x‖ ≤ A := by
    intro x hx
    exact (hstate ε₀ (mem_ball_self hr) x (by simpa only [mem_singleton_iff] using hx.2)).value_bound
  have hnextbound : ∀ x ∈ Icc a z \ {0}, ‖Dnext x‖ ≤ A := by
    intro x hx
    exact (hstate ε₀ (mem_ball_self hr) x (by simpa only [mem_singleton_iff] using hx.2)).next_bound
  have hi₀ := integrableOn_box_off_zero_bound a z (D ε₀) A (hD ε₀ (mem_ball_self hr)) hzero
  have hi₁ := integrableOn_box_off_zero_bound a z Dnext A hDnext hnextbound
  have hcurr (x : Fin (n + 1) → ℝ) (_hx : x ∈ Icc a z) (hx0 : x ∉ ({0} : Set (Fin (n + 1) → ℝ))) :
      D' ε₀ x - (∑ i, F' i x (Pi.single i 1)) = isotropicRadialDerivative α ε₀ * Dnext x := by
    have hs := hstate ε₀ (mem_ball_self hr) x (by simpa only [mem_singleton_iff] using hx0)
    exact centered_radial_current_identity _ _ ρ _ _ _ x hs.flux (hs.current (Fin.last (n + 1)))
  have hfaces (i : Fin (n + 1)) (y : Fin n → ℝ) (_hy : y ∈ Icc (a ∘ i.succAbove) (z ∘ i.succAbove)) :
      F i (i.insertNth (z i) y) = F i (i.insertNth (a i) y) := by
    obtain ⟨hz, ha⟩ := centered_flux_extension_outer_faces (-b - β) β ρ
      (isotropicRadialParameter α ε₀) σ (isotropicRadialDerivative α ε₀) η τ ξ g j i.castSucc hsupport i y
    exact hz.trans ha.symm
  have hparam := box_current_hasDerivAt_off_countable a z haz {0} (Set.countable_singleton _)
    D D' ε₀ r A (2 * A) hr hD hD' hzero hD'bound hDderiv F F'
    (fun i => (hF i).1.continuousOn)
    (fun x hx i => (hF i).2 x (by simpa only [mem_singleton_iff] using hx.2))
    hfaces (isotropicRadialDerivative α ε₀) Dnext hi₁ hcurr
  have hinner : Icc (fun _ : Fin (n + 1) => -b - β - ρ) (fun _ => β - ρ) ⊆ Icc a z := by
    intro x hx
    exact ⟨fun i => by dsimp [a]; linarith [hx.1 i], fun i => by dsimp [z]; linarith [hx.2 i]⟩
  have hzD (ε : ℝ) (x : Fin (n + 1) → ℝ) (hx : x ∉ Icc a z) : D ε x = 0 :=
    centered_transport_density_zero_off_box (-b - β) β ρ _ σ η τ ξ g j hsupport x (fun hh => hx (hinner hh))
  have hzN (x : Fin (n + 1) → ℝ) (hx : x ∉ Icc a z) : Dnext x = 0 :=
    centered_transport_density_zero_off_box (-b - β) β ρ _ σ η τ ξ g (j + 1) hsupport x (fun hh => hx (hinner hh))
  have heD (ε : ℝ) : (∫ x in Icc a z, D ε x) = ∫ x, D ε x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzD ε)
  have heN : (∫ x in Icc a z, Dnext x) = ∫ x, Dnext x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzN
  rw [funext heD, heN] at hparam
  exact ⟨hi₀.integrable_of_forall_notMem_eq_zero (hzD ε₀),
    hi₁.integrable_of_forall_notMem_eq_zero hzN, hparam⟩

end
end IsingBulk.AnisoF002.Isotropic
