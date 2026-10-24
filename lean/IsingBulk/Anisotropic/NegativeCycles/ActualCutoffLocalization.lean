import IsingBulk.Anisotropic.NegativeCycles.RealResidueContinuity

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory

/-- Exact localization of the actual moving inner ellipsoid, followed by the
actual annular Gaussian estimate. No integrability or splitting premise remains. -/
theorem actual_inner_cutoff_localization (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ M c L : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ 0<L ∧ ∀m j : ℕ, ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀b : ContDiffBump (0:ℝ), ∀σ : ℝ,b.rOut≤σ → σ≤ρ^2 →
      let g := fun q => constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q)
      ‖(∫q in {q | constrainedSquaredRadius q<σ},g q)-
          (∫q,(shapeSpatialCutoff b q:ℂ)*g q)‖≤
        ((2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
          ((8*(2*m+1:ℕ):ℝ)/b.rIn)^(j+1))*(2*L)^(2*m) := by
  obtain ⟨a,ha,hcont⟩ := actual_real_residue_uniform_continuous B rootB phi hphi hB hroot hBn r C R hr hR hRr
  obtain ⟨l,M,c,hl,hM,hc,hbound⟩ := actual_real_annular_integral_uniform_bound B rootB phi hphi hB hroot hBn r C R hr hR hRr
  let ρ := min a l
  have hρ : 0<ρ := lt_min ha hl
  have hρa : ρ≤a := min_le_left _ _
  have hρl : ρ≤l := min_le_right _ _
  have hsqa : ρ^2≤a^2 := sq_le_sq₀ hρ.le ha.le |>.mpr hρa
  have hsql : ρ^2≤l^2 := sq_le_sq₀ hρ.le hl.le |>.mpr hρl
  refine ⟨ρ,M,c,l,hρ,hM,hc,hl,?_⟩
  intro m j d hd hd0 P J b σ hb hσ
  dsimp only
  have hct : ContinuousOn (fun q => constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q)) {q | constrainedSquaredRadius q≤ρ^2} := (hcont m j d (hd.trans_le hρa) hd0 P J).mono (fun q hq => hq.trans hsqa)
  rw [constrained_cutoff_localization _ ρ hρ.le hct b σ hb hσ]
  apply hbound m j d (hd.trans_le hρl) P J b.rIn b.rIn_pos
    {q | b.rIn≤constrainedSquaredRadius q ∧ constrainedSquaredRadius q<σ}
    ((isClosed_le continuous_const (constrainedSquaredRadius_contDiff 0).continuous).measurableSet.inter
      (isOpen_lt (constrainedSquaredRadius_contDiff 0).continuous continuous_const).measurableSet)
    (fun _ hq => ⟨hq.1,hq.2.le.trans (hσ.trans hsql)⟩)
  intro q _hq
  have he : (1-(shapeSpatialCutoff b q:ℂ))=((1-shapeSpatialCutoff b q:ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (show shapeSpatialCutoff b q≤1 from b.le_one))]
  linarith [show 0≤shapeSpatialCutoff b q from b.nonneg]

end IsingBulk.Anisotropic.NegativeCycles
