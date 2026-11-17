import IsingBulk.AnisoF002.C03.IsotropicCurrentRegularBuffer
import IsingBulk.AnisoF002.C03.IsotropicCurrentOutsideSupport
import IsingBulk.AnisoF002.C03.IsotropicCenteredCurrentCalculus
import IsingBulk.AnisoF002.C03.IsotropicSmoothCompactIntegral

/-!
# The actual current for a cutoff avoiding total coincidence

No retained-pair count is needed for a fixed particle when the angular
cutoff vanishes near every constant tuple. Actual current regularity
and compact differentiation give every order on the original real
constraint chart. All outer faces vanish by the literal cutoff support.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators ContDiff

structure ActualCurrentRegularAt {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) : Prop where
  smooth : ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g j) q
  analytic : AnalyticAt ℂ (fun s => actualTransportedDensity σ η τ ξ g j (s, q.2)) q.1
  flux : ∀ k, DifferentiableAt ℝ (actualTransportedFlux σ η τ ξ g j k) q
  current : ∀ anchor : Fin N,
    scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection q -
      (∑ k ∈ Finset.univ.erase anchor, scalarPartial (actualTransportedFlux σ η τ ξ g j k)
        (actualAngularDirection k - actualAngularDirection anchor) q) =
      actualTransportedDensity σ η τ ξ g (j + 1) q

theorem actualCurrentRegularAt_outside {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    ActualCurrentRegularAt σ η τ ξ g j q :=
  ⟨(actualTransportedDensity_outside_smooth σ η τ ξ g j q hq).1,
    (actualTransportedDensity_outside_smooth σ η τ ξ g j q hq).2,
    fun k => (actualTransportedFlux_outside_smooth σ η τ ξ g j k q hq).differentiableAt (by simp),
    actualTransportedCurrent_outside σ η τ ξ g j q hq⟩

theorem exists_actual_away_support_regular_current (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ N : ℕ, 0 < N → ∀ g : (Fin N → ℝ) → ℂ, ContDiff ℝ ∞ g →
        (∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β) β) →
        (∀ θ ∈ tsupport g, ∃ i l, θ i ≠ θ l) →
      ∀ s : ℂ, 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ j : ℕ, ∀ θ : Fin N → ℝ, ActualCurrentRegularAt σ η τ ξ g j (s, θ) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_complete_current_regular_buffer S hS
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δ, hδ, hδβ, hreg⟩ := hdata η hη
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro N hN g hg hsupport haway s hs hsd τ hτ ξ hξ σ hσ j θ
  by_cases ht : θ ∈ tsupport g
  · obtain ⟨i, l, hil⟩ := haway θ ht
    obtain ⟨hsm, ha, hf, hc⟩ := hreg N hN s hs hsd τ hτ ξ hξ θ
      (hsupport θ ht) i l hil σ hσ g hg j
    exact ⟨hsm, ha, hf, hc⟩
  · exact actualCurrentRegularAt_outside σ η τ ξ g j (s, θ) ht

theorem isotropicRadialParameter_contDiffAt (α ε : ℝ) (hε : 0 < ε) :
    ContDiffAt ℝ ∞ (isotropicRadialParameter α) ε := by
  have hz : ContDiff ℝ ∞ (isotropicExteriorRadial α) := by
    unfold isotropicExteriorRadial
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.add contDiff_id)).mul contDiff_const
  have hn : isotropicExteriorRadial α ε ≠ 0 :=
    norm_pos_iff.mp (zero_lt_one.trans (isotropicExteriorRadial_exterior α ε hε))
  exact hz.contDiffAt.add (hz.contDiffAt.inv hn)

theorem integrated_actual_current_of_global_regular {n : ℕ}
    (α ε η τ ξ μ L U : ℝ) (σ : ℂ) (g : (Fin (n + 2) → ℝ) → ℂ) (j : ℕ)
    (hε : 0 < ε) (hLU : L ≤ U)
    (hsupport : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc L U)
    (hreg : ∀ k : ℕ, ∀ θ : Fin (n + 2) → ℝ,
      ActualCurrentRegularAt σ η τ ξ g k (isotropicRadialParameter α ε, θ)) :
    Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j
      (isotropicRadialParameter α ε, centeredConstraintAngles μ x)) ∧
    Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g (j + 1)
      (isotropicRadialParameter α ε, centeredConstraintAngles μ x)) ∧
    HasDerivAt (fun u : ℝ => ∫ x : Fin (n + 1) → ℝ, actualTransportedDensity σ η τ ξ g j
      (isotropicRadialParameter α u, centeredConstraintAngles μ x))
      (isotropicRadialDerivative α ε * ∫ x : Fin (n + 1) → ℝ,
        actualTransportedDensity σ η τ ξ g (j + 1)
          (isotropicRadialParameter α ε, centeredConstraintAngles μ x)) ε := by
  let a : Fin (n + 1) → ℝ := fun _ => L - μ - 1
  let z : Fin (n + 1) → ℝ := fun _ => U - μ + 1
  have haz : a ≤ z := fun _ => by dsimp [a, z]; linarith
  let K := Icc a z
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  let D : ℝ × (Fin (n + 2) → ℝ) → ℂ := fun p =>
    actualTransportedDensity σ η τ ξ g j (isotropicRadialParameter α p.1, p.2)
  let Q : (Fin (n + 1) → ℝ) → ℂ := fun x => actualTransportedDensity σ η τ ξ g (j + 1)
    (isotropicRadialParameter α ε, centeredConstraintAngles μ x)
  let T : (Fin (n + 1) → ℝ) → ℂ := fun x => isotropicRadialDerivative α ε *
    scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection
      (isotropicRadialParameter α ε, centeredConstraintAngles μ x)
  let F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ := fun i x =>
    isotropicRadialDerivative α ε * actualTransportedFlux σ η τ ξ g j i.castSucc
      (isotropicRadialParameter α ε, centeredConstraintAngles μ x)
  let F' := fun i x => fderiv ℝ (F i) x
  have hD (θ : Fin (n + 2) → ℝ) : ContDiffAt ℝ 1 D (ε, θ) := by
    have hm : ContDiffAt ℝ ∞ (fun p : ℝ × (Fin (n + 2) → ℝ) =>
        (isotropicRadialParameter α p.1, p.2)) (ε, θ) :=
      ((isotropicRadialParameter_contDiffAt α ε hε).comp (ε, θ) contDiffAt_fst).prodMk contDiffAt_snd
    have hall : ContDiffAt ℝ ∞ D (ε, θ) := by
      exact ContDiffAt.comp (g := actualTransportedDensity σ η τ ξ g j)
        (f := fun p : ℝ × (Fin (n + 2) → ℝ) => (isotropicRadialParameter α p.1, p.2))
        (ε, θ) (hreg j θ).smooth hm
    exact hall.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hQ : Continuous Q := continuous_iff_continuousAt.mpr fun x =>
    ((hreg (j + 1) _).smooth.continuousAt.comp
      (f := fun y : Fin (n + 1) → ℝ => (isotropicRadialParameter α ε, centeredConstraintAngles μ y))
      (centered_joint_hasFDerivAt _ μ x).continuousAt)
  have hD0 : Continuous (fun x : Fin (n + 1) → ℝ => D (ε, centeredConstraintAngles μ x)) :=
    continuous_iff_continuousAt.mpr fun x => (hD _).continuousAt.comp
      (f := fun y : Fin (n + 1) → ℝ => (ε, centeredConstraintAngles μ y))
      (continuousAt_const.prodMk (centeredConstraintAngles_continuous μ).continuousAt)
  have heT (x : Fin (n + 1) → ℝ) : realParameterPartial D (ε, centeredConstraintAngles μ x) = T x := by
    have h₁ := realParameterPartial_hasDerivAt (hD (centeredConstraintAngles μ x))
    have h₂ := radial_hasDerivAt_scalarPartial (actualTransportedDensity σ η τ ξ g j)
      (centeredConstraintAngles μ x) (isotropicRadialParameter α) ε (isotropicRadialDerivative α ε)
      (isotropicRadialParameter_hasDerivAt α ε hε)
      ((hreg j _).smooth.differentiableAt (by simp)) (hreg j _).analytic.differentiableAt
    exact h₁.unique h₂
  obtain ⟨hTi, hdiff⟩ := integral_hasDerivAt_of_joint_C1 (μ := volume.restrict K)
    (f := D) isCompact_Icc (ae_restrict_mem measurableSet_Icc)
    (centeredConstraintAngles_continuous μ) (fun x _ => hD _)
  have hQi : IntegrableOn Q K volume := hQ.continuousOn.integrableOn_compact isCompact_Icc
  have hDi : IntegrableOn (fun x => D (ε, centeredConstraintAngles μ x)) K volume :=
    hD0.continuousOn.integrableOn_compact isCompact_Icc
  simp only [heT] at hTi hdiff
  have hF (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : DifferentiableAt ℝ (F i) x :=
    (((hreg j _).flux i.castSucc).comp x (centered_joint_hasFDerivAt _ μ x).differentiableAt).const_mul _
  have hfaces (i : Fin (n + 1)) (y : Fin n → ℝ) (_hy : y ∈ Icc (a ∘ i.succAbove) (z ∘ i.succAbove)) :
      F i (i.insertNth (z i) y) = F i (i.insertNth (a i) y) := by
    have hz (v : ℝ) (hv : v < L - μ ∨ U - μ < v) : F i (i.insertNth v y) = 0 := by
      have hx : i.insertNth v y ∉ Icc (fun _ => L - μ) (fun _ => U - μ) := by
        intro hx
        have hl := hx.1 i
        have hu := hx.2 i
        simp only [Fin.insertNth_apply_same] at hl hu
        rcases hv with hv | hv <;> linarith
      dsimp [F]
      rw [centered_transport_flux_zero_off_box L U μ _ σ η τ ξ g j i.castSucc hsupport _ hx, mul_zero]
    rw [hz (z i) (Or.inr (by dsimp [z]; linarith)), hz (a i) (Or.inl (by dsimp [a]; linarith))]
  have hc : (∫ x in K, T x) = ∫ x in K, isotropicRadialDerivative α ε * Q x := by
    apply integrated_current_off_countable a z haz F F' ∅ countable_empty
      (fun i => (continuous_iff_continuousAt.mpr fun x => (hF i x).continuousAt).continuousOn)
      (fun x _ i => (hF i x).hasFDerivAt) hfaces T _ hTi (hQi.const_mul _)
    intro x _ _
    exact centered_radial_current_identity _ _ μ _ _ _ x (hreg j _).flux ((hreg j _).current (Fin.last (n + 1)))
  rw [hc, integral_const_mul] at hdiff
  have hinner : Icc (fun _ : Fin (n + 1) => L - μ) (fun _ => U - μ) ⊆ K := by
    intro x hx
    exact ⟨fun i => by dsimp [a]; linarith [hx.1 i], fun i => by dsimp [z]; linarith [hx.2 i]⟩
  have hzD (u : ℝ) (x : Fin (n + 1) → ℝ) (hx : x ∉ K) : D (u, centeredConstraintAngles μ x) = 0 :=
    centered_transport_density_zero_off_box L U μ _ σ η τ ξ g j hsupport x (fun hh => hx (hinner hh))
  have hzQ (x : Fin (n + 1) → ℝ) (hx : x ∉ K) : Q x = 0 :=
    centered_transport_density_zero_off_box L U μ _ σ η τ ξ g (j + 1) hsupport x (fun hh => hx (hinner hh))
  have heD (u : ℝ) : (∫ x in K, D (u, centeredConstraintAngles μ x)) = ∫ x, D (u, centeredConstraintAngles μ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzD u)
  have heQ : (∫ x in K, Q x) = ∫ x, Q x := setIntegral_eq_integral_of_forall_compl_eq_zero hzQ
  rw [funext heD, heQ] at hdiff
  exact ⟨hDi.integrable_of_forall_notMem_eq_zero (hzD ε), hQi.integrable_of_forall_notMem_eq_zero hzQ, hdiff⟩

end
end IsingBulk.AnisoF002.Isotropic
