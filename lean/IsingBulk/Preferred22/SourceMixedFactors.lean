import IsingBulk.Preferred22.FrameDomain

/-! The finite mixed-regularity base of the actual signed-minor recursion.
Every factor is the original real-cutoff/physical-source expression. The
coefficient of the empty minor is handled directly, without dividing by a
determinant that vanishes on partial collisions. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem PreferredFramePoint.inverse_analytic {N : ℕ} {τ δ : ℝ} {p m : ℝ → ℝ}
    {s : ℂ} {θ : Fin N → ℝ} (h : PreferredFramePoint τ δ p m s θ) (i : Fin N) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i) :=
  preferred_global_one_sided_joint_analytic s (deformedAngles τ p m θ i) δ
    h.delta_pos h.delta_lt h.trace_re h.trace_im h.trace_cap
    (by simpa only [deformedAngles_re] using (h.angles i).1)
    (by simpa only [deformedAngles_re] using (h.angles i).2) (h.upper i)

theorem PreferredFramePoint.phase_inside {N : ℕ} {τ δ : ℝ} {p m : ℝ → ℝ}
    {s : ℂ} {θ : Fin N → ℝ} (h : PreferredFramePoint τ δ p m s θ) (i : Fin N) :
    ‖Complex.exp (-Complex.I*preferredRegularPhase s (preferredSourceCoordinate τ p m s θ i))‖<1 := by
  rw [preferred_source_regular_phase_eq s τ p m θ δ h.delta_pos h.delta_lt h.trace_re
    h.trace_cap h.angles h.upper i]
  rw [preferredSourcePhase,preferredArccos_physical_upper _ (h.upper i)]
  exact physicalRoot_inside (Or.inl (h.upper i).ne')

/-- Complex analytic functions in the genuine (s,q) variables pull back to
joint real C-infinity functions which remain holomorphic in s. -/
theorem preferred_analytic_pullback_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : ∀ z∈Ω, AnalyticAt ℂ F (z.1,preferredSourceCoordinate τ p m z.1 z.2)) :
    PreferredMixedSmoothOn (fun z => F (z.1,preferredSourceCoordinate τ p m z.1 z.2)) Ω := by
  intro z hz
  have h := hpoint z hz
  have hχR := preferredSourceCoordinate_contDiffAt τ p m hp hm z.1 z.2 h.trace_im h.upper
  have hχC := preferredSourceCoordinate_parameter_analyticAt τ p m z.1 z.2 h.trace_im h.upper
  constructor
  · exact ContDiffAt.comp
      (f := fun z : ℂ × (Fin N → ℝ) => (z.1,preferredSourceCoordinate τ p m z.1 z.2))
      (g := F) z ((hF z hz).contDiffAt.restrict_scalars ℝ) (contDiffAt_fst.prodMk hχR)
  · exact DifferentiableAt.comp
      (f := fun s : ℂ => (s,preferredSourceCoordinate τ p m s z.2)) (g := F)
      z.1 (hF z hz).differentiableAt (differentiableAt_id.prodMk hχC.differentiableAt)

/-- Actual regular kernel and one-body pullbacks, including their complete
mixed real/complex calculus at every physically legal source point. -/
theorem preferred_regular_factors_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    (∀ a : Fin N × Fin N, PreferredMixedSmoothOn
      (fun z => preferredSourceRegularKernel τ p m z.1 z.2 a.1 a.2) Ω) ∧
    (∀ i : Fin N, PreferredMixedSmoothOn
      (fun z => preferredRegularOneBody z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω) := by
  constructor
  · intro a
    apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun z => preferredRegularKernel z.1 z.2 a.1 a.2)
    intro z hz
    have h := hpoint z hz
    exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp
      (preferredRegularKernel_analyticAt z.1 _ h.inverse_analytic
        (preferredMovingBranch_analyticAt_upper z.1 h.trace_im) h.phase_inside) a.1) a.2
  · intro i
    apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun z => preferredRegularOneBody z.1 (z.2 i))
    intro z hz
    have h := hpoint z hz
    have hq : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2) :=
      (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt _)
    exact AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i))
      (g := fun x : ℂ × ℂ => preferredRegularOneBody x.1 x.2)
      (preferredRegularOneBody_analyticAt z.1 _ (h.inverse_analytic i)
        (preferredMovingBranch_analyticAt_upper z.1 h.trace_im) (h.phase_inside i))
      (analyticAt_fst.prod hq)

/-- The initial coefficient retains all smooth real cutoff factors and all
actual one-body factors. No division by the kernel determinant is used. -/
theorem preferredRegularSeedCoefficient_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z => preferredRegularSeedCoefficient τ η p m r z.1 z.2) Ω := by
  have hbody := (preferred_regular_factors_mixed τ δ p m hp hm Ω hpoint).2
  have hw : ContDiff ℝ ∞ (fun x : Fin N → ℝ => preferredCellWeight .right η p m r x) := by
    unfold preferredCellWeight preferredLowerWeight preferredRightWeight lowerWeight occupancy
    fun_prop
  have hwc : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => (preferredCellWeight .right η p m r z.2:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_snd)
  intro z hz
  constructor
  · exact (hwc.contDiffAt.mul (contDiffAt_prod (fun i _ => (hbody i z hz).1))).div_const _
  · change DifferentiableAt ℂ (fun t => (preferredCellWeight .right η p m r z.2:ℂ) *
        (∏ i, preferredRegularOneBody t (preferredSourceCoordinate τ p m t z.2 i)) /
          ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))) z.1
    exact ((differentiableAt_const (𝕜:=ℂ) (x:=z.1)
      (preferredCellWeight .right η p m r z.2:ℂ)).mul
        (DifferentiableAt.fun_finsetProd (fun i _ => (hbody i z hz).2))).div_const _

/-- The complete finite smoothness base required by the actual marked-word
recursion. Raw collective analyticity is the only additional local premise;
it is discharged at actual source points by the constructed neighborhood. -/
theorem preferredMarkedBaseSmoothness_of_geometry {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ z∈Ω, AnalyticAt ℂ
      (fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) :
    PreferredMarkedBaseSmoothness τ η p m r Ω := by
  have hBm (a : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω :=
    preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun x => preferredResidualCollective x.1 x.2 a)
      (fun z hz => analyticAt_pi_iff.mp (hB z hz) a)
  have hMi (i a : Fin N) : PreferredMixedSmoothOn
      (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i a) Ω := by
    intro z hz
    have hh := preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 (hpoint z hz).matrix
    refine ⟨(contDiffAt_pi.mp (contDiffAt_pi.mp hh i) a).comp z contDiffAt_snd,?_⟩
    exact differentiableAt_const (𝕜:=ℂ) (x:=z.1) ((preferredContourMatrix τ p m z.2)⁻¹ i a)
  have hv (a : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 a)) Ω := by
    intro z hz
    have h := hpoint z hz
    exact ⟨contDiffAt_pi.mp
      (preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2
        h.trace_im h.upper h.inverse_analytic).1 a,
      (analyticAt_pi_iff.mp
        (preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2
          h.trace_im h.upper h.inverse_analytic).1 a).differentiableAt⟩
  have hu (a : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredSourceUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 a)) Ω := by
    intro z hz
    have h := hpoint z hz
    exact ⟨contDiffAt_pi.mp
      (preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2
        h.trace_im h.upper h.inverse_analytic).2 a,
      (analyticAt_pi_iff.mp
        (preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2
          h.trace_im h.upper h.inverse_analytic).2 a).differentiableAt⟩
  refine ⟨?_,?_,(preferred_regular_factors_mixed τ δ p m hp hm Ω hpoint).1,
    preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint⟩
  · intro i
    have hh := PreferredMixedSmoothOn.sum
      (fun a => (hMi i a).mul ((hu a).add ((hv a).mul (hBm a))))
    intro z hz
    simpa only [preferredSourceAngularField,preferredAngularRepresentative,
      preferredResidualField,Matrix.mulVec,dotProduct] using
      (show ContDiffAt ℝ ∞ (fun z => -(∑ a, (preferredContourMatrix τ p m z.2)⁻¹ i a *
        (preferredSourceUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 a)+
          preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 a)*
            preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a))) z ∧
        DifferentiableAt ℂ (fun s => -(∑ a, (preferredContourMatrix τ p m z.2)⁻¹ i a *
          (preferredSourceUDot s (preferredSourceCoordinate τ p m s z.2 a)+
            preferredSourceUQ s (preferredSourceCoordinate τ p m s z.2 a)*
              preferredResidualCollective s (preferredSourceCoordinate τ p m s z.2) a))) z.1
        from ⟨(hh z hz).1.neg,(hh z hz).2.neg⟩)
  · exact PreferredMixedSmoothOn.sum (fun a => PreferredMixedSmoothOn.sum
      (fun i => ((hMi i a).mul (hv a)).mul ((hBm a).coordinate hΩ i)))

end
end IsingBulk.Preferred22
