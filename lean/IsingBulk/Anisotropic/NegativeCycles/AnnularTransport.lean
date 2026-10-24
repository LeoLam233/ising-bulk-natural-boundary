import IsingBulk.Anisotropic.NegativeCycles.CylinderCutoff
import IsingBulk.Anisotropic.NegativeCycles.CutoffBound

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set MeasureTheory
open scoped BigOperators

/-- Only the actual cutoff annulus requires density and Jacobian bounds. -/
theorem cylinder_error_integral_bound {n : ℕ} (hn : 0<n)
    (bump : ContDiffBump (0:ℝ)) (f : (Fin n→ℂ)→ℂ)
    (H : ParameterSpace n→Fin n→ℂ) {a b : ParameterSpace n}
    (ha : a 0=0) (hb : b 0=1)
    {K F L : ℝ} (hK : 0≤K) (hF : 0≤F) (hL : 0≤L)
    (hbound : ∀x∈Icc a b, x∈tsupport (cylinderCutoff bump) →
      bump.rIn≤squaredRadius (fun i => x i.succ) →
      (∀i, ‖fderiv ℝ (cylinderCutoff bump) x (Pi.single i 1)‖≤K) ∧
      ‖f (H x)‖≤F ∧ (∀i j, ‖fderiv ℝ H x (Pi.single i 1) j‖≤L)) :
    ‖∫ x in Icc a b, cutoffError (cylinderCutoff bump) (chainPullback (densityForm f) H) x‖≤
      ((n+1)*K*F*Real.sqrt (((n:ℝ)*L^2)^n))*(volume (Icc a b)).toReal := by
  have he : ∀x∈Icc a b,
      ‖cutoffError (cylinderCutoff bump) (chainPullback (densityForm f) H) x‖≤
        (n+1)*K*F*Real.sqrt (((n:ℝ)*L^2)^n) := by
    intro x hx
    by_cases hs : x∈tsupport (cylinderCutoff bump)
    · by_cases hq : squaredRadius (fun i => x i.succ)<bump.rIn
      · have ht : x 0∈Icc (0:ℝ) 1 := by
          exact ⟨by simpa [ha] using hx.1 0,by simpa [hb] using hx.2 0⟩
        rw [cylinderCutoff_error_inner_zero bump _ ht hq,norm_zero]
        positivity
      · obtain ⟨hc,hf,hH⟩ := hbound x hx hs (le_of_not_gt hq)
        exact norm_cutoffError_density_le hn _ f H x hK hF hL hc hf hH
    · rw [cutoffError_eq_zero_of_notMem_tsupport _ hs,norm_zero]
      positivity
  let _ : IsFiniteMeasure (volume.restrict (Icc a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Icc a b)) ((ae_restrict_mem measurableSet_Icc).mono he)
  simpa only [Measure.real,Measure.restrict_apply_univ] using hh

/-- The genuine cap comparison, specialized to a fixed-radius spatial cutoff. -/
theorem cylinder_caps_transport {n : ℕ}
    (bump : ContDiffBump (0:ℝ)) (f : (Fin n→ℂ)→ℂ)
    (H : ParameterSpace n→Fin n→ℂ)
    (hf : ∀x, x 0∈Icc (-1/2:ℝ) (3/2) → squaredRadius (fun i => x i.succ)≤bump.rOut →
      DifferentiableAt ℂ f (H x))
    (hH : ∀x, x 0∈Icc (-1/2:ℝ) (3/2) → squaredRadius (fun i => x i.succ)≤bump.rOut →
      ContDiffAt ℝ 2 H x)
    {a b : ParameterSpace n} (hab : a≤b)
    (hfront : ∀i : Fin n, bump.rOut≤(b i.succ)^2)
    (hback : ∀i : Fin n, bump.rOut≤(a i.succ)^2) :
    boxCapIntegral (fun x => cylinderCutoff bump x • chainPullback (densityForm f) H x) a b (b 0)-
      boxCapIntegral (fun x => cylinderCutoff bump x • chainPullback (densityForm f) H x) a b (a 0)=
        ∫ x in Icc a b, cutoffError (cylinderCutoff bump) (chainPullback (densityForm f) H) x := by
  apply holomorphic_cutoff_caps_transport (cylinderCutoff_contDiff bump 1) f H
    (fun x hx => hf x (cylinderCutoff_tsupport_subset bump hx).1 (cylinderCutoff_tsupport_subset bump hx).2)
    (fun x hx => hH x (cylinderCutoff_tsupport_subset bump hx).1 (cylinderCutoff_tsupport_subset bump hx).2) hab
  · intro i q
    exact cylinderCutoff_zero_of_coordinate bump i (by simpa using hfront i)
  · intro i q
    exact cylinderCutoff_zero_of_coordinate bump i (by simpa using hback i)

end IsingBulk.Anisotropic.NegativeCycles
