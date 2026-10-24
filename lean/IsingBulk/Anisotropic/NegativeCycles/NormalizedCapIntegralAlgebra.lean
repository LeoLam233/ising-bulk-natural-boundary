import IsingBulk.Anisotropic.NegativeCycles.ActualNormalizedCapIntegrability
import IsingBulk.Anisotropic.NegativeNormalForm.PhysicalComplexPeriod

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators

/-- Integrability of the error is deduced from the actual cap and model, rather
than assumed from a norm estimate with an unproved measurability premise. -/
theorem normalized_integral_split {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (F χ D k : X→ℂ) (center : ℂ) (hc : center≠0)
    (he : ∀x,F x=center*χ x*D x*k x)
    (hF : Integrable F μ) (hk : Integrable (fun x=>χ x*k x) μ) :
    Integrable (fun x=>χ x*(D x-1)*k x) μ ∧
      (∫x,F x ∂μ)=center*((∫x,χ x*k x ∂μ)+(∫x,χ x*(D x-1)*k x ∂μ)) := by
  have hdiff : (fun x=>χ x*(D x-1)*k x)=(fun x=>F x/center-χ x*k x) := by
    funext x
    rw [he x]
    field_simp [hc]
  have hi : Integrable (fun x=>χ x*(D x-1)*k x) μ := by
    rw [hdiff]
    exact (hF.div_const center).sub hk
  refine ⟨hi,?_⟩
  have hf : F=(fun x=>center*(χ x*k x+χ x*(D x-1)*k x)) := by
    funext x
    rw [he x]
    ring
  rw [hf,integral_const_mul,integral_add hk hi]

theorem quadraticModel_cutoff_integrable_positive {n : ℕ} (j : ℕ)
    (τ : ℝ) (hτ : 0<τ) (c : ℂ) (hc : 0≤c.re) (b : ContDiffBump (0:ℝ)) :
    Integrable (fun q : Fin n→ℝ=>(shapeSpatialCutoff b q:ℂ)*quadraticModelKernel n j τ c q) := by
  have hden (q : Fin n→ℝ) : (τ:ℂ)+c*(constrainedSquaredRadius q:ℂ)≠0 := by
    have hre : 0<((τ:ℂ)+c*(constrainedSquaredRadius q:ℂ)).re := by
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact add_pos_of_pos_of_nonneg hτ (mul_nonneg hc (constrainedSquaredRadius_nonneg q))
    intro hz
    rw [hz,Complex.zero_re] at hre
    linarith
  have hg : Continuous (quadraticModelKernel n j τ c) := by
    unfold quadraticModelKernel
    apply Continuous.div
    · unfold firstVandermonde
      fun_prop
    · exact (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp (constrainedSquaredRadius_contDiff 0).continuous))).pow _
    · intro q
      exact pow_ne_zero _ (hden q)
  let ρ := b.rOut+1
  have hρ : 0<ρ := by dsimp [ρ]; linarith [b.rOut_pos]
  have hb : b.rOut≤ρ^2 := by dsimp [ρ]; nlinarith [b.rOut_pos]
  let K : Set (Fin n→ℝ) := {q | constrainedSquaredRadius q≤ρ^2}
  have hK : IsCompact K := isCompact_constrained_squared_sublevel ρ hρ.le
  have hcont := (Complex.continuous_ofReal.comp (shapeSpatialCutoff_contDiff (n := n) b 0).continuous).mul hg
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp
    (hcont.continuousOn.integrableOn_compact (μ := volume) hK)
  intro q hq
  by_contra hn
  have hz := shapeSpatialCutoff_zero b (hb.trans (le_of_not_ge hn))
  exact hq (by simp [hz])

/-- The box cap in the Stokes comparison is exactly the global cutoff integral. -/
theorem shape_cutoff_integral_box {n : ℕ} (b : ContDiffBump (0:ℝ))
    (ρ : ℝ) (hρ : 0≤ρ) (hb : b.rOut≤ρ^2) (g : (Fin n→ℝ)→ℂ) :
    (∫q in Icc (fun _ : Fin n=>-ρ) (fun _=>ρ),(shapeSpatialCutoff b q:ℂ)*g q)=
      ∫q,(shapeSpatialCutoff b q:ℂ)*g q := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  have hn : ¬constrainedSquaredRadius q≤ρ^2 := by
    intro h
    have hi := (constrainedSquaredRadius_coordinates_le q hρ h).1
    exact hq ⟨fun i=>(abs_le.mp (hi i)).1,fun i=>(abs_le.mp (hi i)).2⟩
  simp [shapeSpatialCutoff_zero b (hb.trans (le_of_not_ge hn))]

end IsingBulk.Anisotropic.NegativeCycles
