import IsingBulk.Analysis.LieAlgebra
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Coordinate integration for rc4 Appendix D. Boundary flux is an actual sum
of face integrals. The exhaustion limit is a separate convergence hypothesis;
it is not the desired parameter-derivative identity. -/
namespace IsingBulk.Lie
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

abbrev AngularSpace (n : ℕ) := Fin (n+1) → ℝ

def divergence {n : ℕ} (F : AngularSpace n → Fin (n+1) → ℂ)
    (x : AngularSpace n) : ℂ :=
  ∑ i, fderiv ℝ (fun y => F y i) x (Pi.single i 1)

def boundaryFlux {n : ℕ} (a b : AngularSpace n)
    (F : AngularSpace n → Fin (n+1) → ℂ) : ℂ :=
  ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    F (i.insertNth (b i) x) i) -
    ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) x) i)

theorem integral_divergence_eq_flux {n : ℕ} (a b : AngularSpace n) (hab : a ≤ b)
    (F : AngularSpace n → Fin (n+1) → ℂ)
    (hc : ∀ i, ContinuousOn (fun x => F x i) (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i => Ioo (a i) (b i)),
      ∀ i, DifferentiableAt ℝ (fun y => F y i) x)
    (hi : IntegrableOn (divergence F) (Icc a b)) :
    (∫ x in Icc a b, divergence F x) = boundaryFlux a b F := by
  exact integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (fun i x => F x i) (fun i x => fderiv ℝ (fun y => F y i) x)
    ∅ countable_empty hc (fun x hx i => (hd x hx.1 i).hasFDerivAt) hi

/-- Opposite faces are identified in a periodic coordinate domain. -/
theorem periodic_boundaryFlux_zero {n : ℕ} (a b : AngularSpace n)
    (F : AngularSpace n → Fin (n+1) → ℂ)
    (hperiodic : ∀ i x, F (i.insertNth (b i) x) i = F (i.insertNth (a i) x) i) :
    boundaryFlux a b F = 0 := by
  simp only [boundaryFlux, hperiodic, sub_self, Finset.sum_const_zero]

/-- Finite rectangular excisions: Stokes is proved on every actual box before
taking the exhaustion limit. Internal faces may be canceled in the flux sum. -/
theorem integral_divergence_zero_of_exhaustion {n : ℕ}
    (μ : Measure (AngularSpace n)) (F : AngularSpace n → Fin (n+1) → ℂ)
    (count : ℕ → ℕ) (a b : (k : ℕ) → Fin (count k) → AngularSpace n)
    (hab : ∀ k r, a k r ≤ b k r)
    (hc : ∀ k r i, ContinuousOn (fun x => F x i) (Icc (a k r) (b k r)))
    (hd : ∀ k r x, x ∈ pi univ (fun i => Ioo (a k r i) (b k r i)) →
      ∀ i, DifferentiableAt ℝ (fun y => F y i) x)
    (hi : ∀ k r, IntegrableOn (divergence F) (Icc (a k r) (b k r)))
    (hexhaust : Tendsto (fun k => ∑ r, ∫ x in Icc (a k r) (b k r), divergence F x)
      atTop (𝓝 (∫ x, divergence F x ∂μ)))
    (hflux : Tendsto (fun k => ∑ r, boundaryFlux (a k r) (b k r) F) atTop (𝓝 0)) :
    (∫ x, divergence F x ∂μ) = 0 := by
  have heq : (fun k => ∑ r, ∫ x in Icc (a k r) (b k r), divergence F x) =
      (fun k => ∑ r, boundaryFlux (a k r) (b k r) F) := by
    funext k
    apply Finset.sum_congr rfl
    intro r _
    exact integral_divergence_eq_flux _ _ (hab k r) F (hc k r) (hd k r) (hi k r)
  rw [heq] at hexhaust
  exact tendsto_nhds_unique hexhaust hflux

def lieStep {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  deriv (fun t => A t x) s - divergence (fun y i => V s y i * A s y) x

/-- Dominated differentiation plus a proved zero divergence integral yields the
first-stage identity. The flux-to-zero implication is supplied above by Stokes. -/
theorem first_stage_of_zero_divergence {n : ℕ} (μ : Measure (AngularSpace n))
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (U : Set ℂ) (bound : AngularSpace n → ℝ)
    (hU : U ∈ 𝓝 s)
    (hmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (A t) μ)
    (hint : Integrable (A s) μ)
    (hdmeas : AEStronglyMeasurable (fun x => deriv (fun t => A t x) s) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ U, ‖deriv (fun r => A r x) t‖ ≤ bound x)
    (hbi : Integrable bound μ)
    (hdiff : ∀ᵐ x ∂μ, ∀ t ∈ U, DifferentiableAt ℂ (fun r => A r x) t)
    (hdivint : Integrable (divergence (fun y i => V s y i * A s y)) μ)
    (hdivzero : (∫ x, divergence (fun y i => V s y i * A s y) x ∂μ) = 0) :
    HasDerivAt (fun t => ∫ x, A t x ∂μ) (∫ x, lieStep V A s x ∂μ) s := by
  obtain ⟨hdi, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hU hmeas hint hdmeas hbound hbi (hdiff.mono fun x hx t ht => (hx t ht).hasDerivAt)
  simpa only [lieStep, integral_sub hdi hdivint, hdivzero, sub_zero] using hderiv

/-- A genuine periodic-box instance, with no assumed derivative/integral identity. -/
theorem first_stage_periodic_box {n : ℕ} (a b : AngularSpace n) (hab : a ≤ b)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (U : Set ℂ) (bound : AngularSpace n → ℝ) (hU : U ∈ 𝓝 s)
    (hmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (A t) (volume.restrict (Icc a b)))
    (hint : IntegrableOn (A s) (Icc a b))
    (hdmeas : AEStronglyMeasurable (fun x => deriv (fun t => A t x) s)
      (volume.restrict (Icc a b)))
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ t ∈ U,
      ‖deriv (fun r => A r x) t‖ ≤ bound x)
    (hbi : IntegrableOn bound (Icc a b))
    (hdiff : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ t ∈ U,
      DifferentiableAt ℂ (fun r => A r x) t)
    (hc : ∀ i, ContinuousOn (fun x => V s x i * A s x) (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i => Ioo (a i) (b i)), ∀ i,
      DifferentiableAt ℝ (fun y => V s y i * A s y) x)
    (hi : IntegrableOn (divergence (fun y i => V s y i * A s y)) (Icc a b))
    (hp : ∀ i x, V s (i.insertNth (b i) x) i * A s (i.insertNth (b i) x) =
      V s (i.insertNth (a i) x) i * A s (i.insertNth (a i) x)) :
    HasDerivAt (fun t => ∫ x in Icc a b, A t x)
      (∫ x in Icc a b, lieStep V A s x) s := by
  apply first_stage_of_zero_divergence _ V A s U bound hU hmeas hint hdmeas
    hbound hbi hdiff hi
  rw [integral_divergence_eq_flux a b hab _ hc hd hi,
    periodic_boundaryFlux_zero a b _ hp]

/-- Checkable local regularity data for dominated complex differentiation. -/
structure DifferentiationData {n : ℕ} (μ : Measure (AngularSpace n))
    (A : ℂ → AngularSpace n → ℂ) (s : ℂ) where
  neighborhood : Set ℂ
  mem_nhds : neighborhood ∈ 𝓝 s
  bound : AngularSpace n → ℝ
  measurable : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (A t) μ
  integrable : Integrable (A s) μ
  derivative_measurable : AEStronglyMeasurable (fun x => deriv (fun t => A t x) s) μ
  derivative_bound : ∀ᵐ x ∂μ, ∀ t ∈ neighborhood, ‖deriv (fun r => A r x) t‖ ≤ bound x
  bound_integrable : Integrable bound μ
  differentiable : ∀ᵐ x ∂μ, ∀ t ∈ neighborhood, DifferentiableAt ℂ (fun r => A r x) t

/-- An explicit rectangular exhaustion and its boundary-flux limit. The
integral convergence field must still be established for a geometric excision. -/
structure FluxExhaustion {n : ℕ} (μ : Measure (AngularSpace n))
    (F : AngularSpace n → Fin (n+1) → ℂ) where
  count : ℕ → ℕ
  lower : (k : ℕ) → Fin (count k) → AngularSpace n
  upper : (k : ℕ) → Fin (count k) → AngularSpace n
  ordered : ∀ k r, lower k r ≤ upper k r
  continuous : ∀ k r i, ContinuousOn (fun x => F x i) (Icc (lower k r) (upper k r))
  differentiable : ∀ k r x, x ∈ pi univ (fun i => Ioo (lower k r i) (upper k r i)) →
    ∀ i, DifferentiableAt ℝ (fun y => F y i) x
  integrable : ∀ k r, IntegrableOn (divergence F) (Icc (lower k r) (upper k r))
  convergence : Tendsto (fun k => ∑ r, ∫ x in Icc (lower k r) (upper k r), divergence F x)
    atTop (𝓝 (∫ x, divergence F x ∂μ))
  flux_vanishes : Tendsto (fun k => ∑ r, boundaryFlux (lower k r) (upper k r) F) atTop (𝓝 0)

theorem FluxExhaustion.integral_zero {n : ℕ} {μ : Measure (AngularSpace n)}
    {F : AngularSpace n → Fin (n+1) → ℂ} (h : FluxExhaustion μ F) :
    (∫ x, divergence F x ∂μ) = 0 :=
  integral_divergence_zero_of_exhaustion μ F h.count h.lower h.upper h.ordered
    h.continuous h.differentiable h.integrable h.convergence h.flux_vanishes

theorem first_stage_excision {n : ℕ} (μ : Measure (AngularSpace n))
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ) (s : ℂ)
    (h : DifferentiationData μ A s)
    (hf : FluxExhaustion μ (fun x i => V s x i * A s x))
    (hi : Integrable (divergence (fun x i => V s x i * A s x)) μ) :
    HasDerivAt (fun t => ∫ x, A t x ∂μ) (∫ x, lieStep V A s x ∂μ) s :=
  first_stage_of_zero_divergence μ V A s h.neighborhood h.bound h.mem_nhds
    h.measurable h.integrable h.derivative_measurable h.derivative_bound
    h.bound_integrable h.differentiable hi hf.integral_zero

/-- Every stage differentiates the full preceding density and the s-dependent
field. Stage hypotheses are analytic regularity and actual fluxes, not the
desired first-derivative identity. This global-parameter interface still needs
localization to the manuscript's parameter neighborhood. -/
theorem iterate_lieStep_integral {n : ℕ} (μ : Measure (AngularSpace n))
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ) (j : ℕ)
    (hd : ∀ k < j, ∀ s, DifferentiationData μ ((lieStep V)^[k] A) s)
    (hf : ∀ k < j, ∀ s, FluxExhaustion μ
      (fun x i => V s x i * ((lieStep V)^[k] A) s x))
    (hi : ∀ k < j, ∀ s, Integrable (divergence
      (fun x i => V s x i * ((lieStep V)^[k] A) s x)) μ) :
    (fun s => ∫ x, ((lieStep V)^[j] A) s x ∂μ) =
      (deriv^[j] (fun s => ∫ x, A s x ∂μ)) := by
  apply iterate_integral_of_stage_identities (lieStep V) deriv
    (fun B s => ∫ x, B s x ∂μ) A j
  intro k hk
  funext s
  exact (first_stage_excision μ V _ s (hd k hk s) (hf k hk s) (hi k hk s)).deriv.symm

/-- Local-parameter iteration, so regularity away from the parameter
neighborhood is not required. -/
theorem iterate_lieStep_integral_on {n : ℕ} (μ : Measure (AngularSpace n))
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (j : ℕ)
    (hd : ∀ k < j, ∀ s ∈ U, DifferentiationData μ ((lieStep V)^[k] A) s)
    (hf : ∀ k < j, ∀ s ∈ U, FluxExhaustion μ
      (fun x i => V s x i * ((lieStep V)^[k] A) s x))
    (hi : ∀ k < j, ∀ s ∈ U, Integrable (divergence
      (fun x i => V s x i * ((lieStep V)^[k] A) s x)) μ) :
    EqOn (fun s => ∫ x, ((lieStep V)^[j] A) s x ∂μ)
      (deriv^[j] (fun s => ∫ x, A s x ∂μ)) U := by
  induction j with
  | zero => intro s _; rfl
  | succ j ih =>
    have hprev := ih (fun k hk => hd k (by omega))
      (fun k hk => hf k (by omega)) (fun k hk => hi k (by omega))
    intro s hs
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      _ = deriv (fun t => ∫ x, ((lieStep V)^[j] A) t x ∂μ) s :=
        (first_stage_excision μ V _ s (hd j (by omega) s hs)
          (hf j (by omega) s hs) (hi j (by omega) s hs)).deriv.symm
      _ = _ := (hprev.eventuallyEq_of_mem (hU.mem_nhds hs)).deriv_eq

/-- Integral convergence for genuine finite box unions follows from monotone
exhaustion, with overlaps allowed only on null sets. -/
theorem rectangular_exhaustion_convergence {n : ℕ} (f : AngularSpace n → ℂ)
    (count : ℕ → ℕ) (a b : (k : ℕ) → Fin (count k) → AngularSpace n)
    (hdisjoint : ∀ k, Pairwise (fun r t => AEDisjoint volume
      (Icc (a k r) (b k r)) (Icc (a k t) (b k t))))
    (hmono : Monotone (fun k => ⋃ r, Icc (a k r) (b k r)))
    (hi : IntegrableOn f (⋃ k, ⋃ r, Icc (a k r) (b k r))) :
    Tendsto (fun k => ∑ r, ∫ x in Icc (a k r) (b k r), f x) atTop
      (𝓝 (∫ x in ⋃ k, ⋃ r, Icc (a k r) (b k r), f x)) := by
  have hconv := tendsto_setIntegral_of_monotone
    (fun k => MeasurableSet.iUnion (fun _ => measurableSet_Icc)) hmono hi
  have heq : ∀ k, (∫ x in ⋃ r, Icc (a k r) (b k r), f x) =
      ∑ r, ∫ x in Icc (a k r) (b k r), f x := by
    intro k
    have hk := integral_iUnion_ae (fun _ => measurableSet_Icc.nullMeasurableSet)
      (hdisjoint k) (hi.mono_set (subset_iUnion (fun k => ⋃ r, Icc (a k r) (b k r)) k))
    simpa only [tsum_fintype] using hk
  simpa only [heq] using hconv

end
end IsingBulk.Lie
