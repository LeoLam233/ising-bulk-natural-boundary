import IsingBulk.Anisotropic.NegativeCycles.RealAnnularIntegralBound

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First Set MeasureTheory

 theorem isCompact_constrained_squared_sublevel {n : ℕ} (ρ : ℝ) (hρ : 0≤ρ) :
    IsCompact {q : Fin n→ℝ | constrainedSquaredRadius q≤ρ^2} := by
  apply IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_le (constrainedSquaredRadius_contDiff 0).continuous continuous_const)
  intro q hq
  have hh := (constrainedSquaredRadius_coordinates_le q hρ hq).1
  exact ⟨fun i => (abs_le.mp (hh i)).1,fun i => (abs_le.mp (hh i)).2⟩

 theorem constrained_cutoff_localization {n : ℕ} (g : (Fin n→ℝ)→ℂ)
    (ρ : ℝ) (hρ : 0≤ρ)
    (hg : ContinuousOn g {q | constrainedSquaredRadius q≤ρ^2})
    (b : ContDiffBump (0:ℝ)) (σ : ℝ) (hb : b.rOut≤σ) (hσ : σ≤ρ^2) :
    (∫q in {q | constrainedSquaredRadius q<σ},g q)-
      (∫q,(shapeSpatialCutoff b q:ℂ)*g q)=
      ∫q in {q | b.rIn≤constrainedSquaredRadius q ∧ constrainedSquaredRadius q<σ},
        (1-(shapeSpatialCutoff b q:ℂ))*g q := by
  have hK := isCompact_constrained_squared_sublevel (n := n) ρ hρ
  have hsub : {q : Fin n→ℝ | constrainedSquaredRadius q<σ}⊆
      {q | constrainedSquaredRadius q≤ρ^2} := fun _ hq => hq.le.trans hσ
  have hi := (hg.integrableOn_compact (μ := volume) hK).mono_set hsub
  have hχ : ContinuousOn (fun q : Fin n→ℝ => (shapeSpatialCutoff b q:ℂ)) {q | constrainedSquaredRadius q≤ρ^2} := (Complex.continuous_ofReal.comp (shapeSpatialCutoff_contDiff (n := n) b 0).continuous).continuousOn
  have hic : IntegrableOn (fun q => (shapeSpatialCutoff b q:ℂ)*g q) {q | constrainedSquaredRadius q<σ} volume := ((hχ.mul hg).integrableOn_compact (μ := volume) hK).mono_set hsub
  have hcut : (∫q in {q : Fin n→ℝ | constrainedSquaredRadius q<σ},(shapeSpatialCutoff b q:ℂ)*g q)=
      ∫q,(shapeSpatialCutoff b q:ℂ)*g q := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hh : σ≤constrainedSquaredRadius q := le_of_not_gt hq
    simp [shapeSpatialCutoff_zero b (hb.trans hh)]
  rw [←hcut,←integral_sub hi hic]
  simp_rw [←one_sub_mul]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    ((isOpen_lt (constrainedSquaredRadius_contDiff 0).continuous continuous_const).measurableSet)
    (fun _ hq => hq.2)
  intro q hq
  have hlow : constrainedSquaredRadius q<b.rIn := by
    by_contra hh
    exact hq.2 ⟨le_of_not_gt hh,hq.1⟩
  simp [shapeSpatialCutoff_one b hlow.le]

end IsingBulk.Anisotropic.NegativeCycles
