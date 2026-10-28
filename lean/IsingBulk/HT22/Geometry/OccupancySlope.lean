import IsingBulk.HT22.Geometry.CompactInverse
import IsingBulk.Preferred22.NegativeCoarea

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter Set IsingBulk.Preferred22

theorem angularInverseRegular_of_upper (S w : ℂ) (δ : ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hS : 0<S.re) (hSδ : S.re<2*Real.cos δ)
    (hlo : -Real.pi-δ≤w.re) (hhi : w.re≤δ) (hW : 0<(S-Complex.cos w).im) :
    AngularInverseRegular S w := by
  let φ := preferredArccos (S-Complex.cos w)
  have ha := IsingBulk.Branch.lowerArccos_analytic_of_upper hW
  obtain ⟨hl,hu⟩ := preferred_half_difference_strip S w δ hδ hδπ hS hSδ hlo hhi hW
  have hdisp : Complex.cos w+Complex.cos φ=S := by rw [cos_preferredArccos]; ring
  have hc : Complex.cos ((w+φ)/2)≠0 := by
    intro hz
    have hh := Complex.cos_add_cos w φ
    rw [hz,mul_zero,zero_mul,hdisp] at hh
    rw [hh,Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  have hsheet := IsingBulk.Branch.lowerArccos_sheet_of_upper hW
  have hs : Complex.sin φ ≠ 0 := by
    have hp := preferred_sine_re_pos_of_strip φ hsheet.2.1 hsheet.2.2.1
    intro hz
    rw [hz,Complex.zero_re] at hp
    exact hp.false
  have hraw := complexRightInverse_analyticAt_of_strip S w φ hdisp hc hl hu
  have hU : AnalyticAt ℂ (complexRightInverse S) (w+φ) :=
    AnalyticAt.comp (f := fun v : ℂ => (S,v))
      (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) hraw (analyticAt_const.prod analyticAt_id)
  have he : complexRightInverse S (w+φ)=w := complexRightInverse_inverse S w φ hdisp hc hl hu
  have hd := hU.differentiableAt.hasDerivAt.ccos.add
    (((hasDerivAt_id (w+φ)).sub hU.differentiableAt.hasDerivAt).ccos)
  have hnear : ∀ᶠ v in 𝓝 (w+φ), Complex.cos (v/2)≠0 :=
    (by fun_prop : ContinuousAt (fun v : ℂ => Complex.cos (v/2)) (w+φ)).eventually_ne hc
  have hconst : (fun v => Complex.cos (complexRightInverse S v)+Complex.cos (v-complexRightInverse S v))
      =ᶠ[𝓝 (w+φ)] (fun _ => S) := by
    filter_upwards [hnear] with v hv
    exact complexRightInverse_dispersion S v hv
  have hder := (hd.congr_of_eventuallyEq hconst.symm).unique (hasDerivAt_const (w+φ) S)
  simp only [Pi.sub_apply,id_eq,he,add_sub_cancel_left] at hder
  have hgap : Complex.sin φ-Complex.sin w≠0 := by
    intro hz
    have heq := sub_eq_zero.mp hz
    rw [heq] at hder
    apply hs
    rw [heq]
    linear_combination -hder
  refine ⟨ha,hc,hl,hu,hs,?_⟩
  unfold preferredPhaseSlope
  change 1+-Complex.sin w/Complex.sin φ≠0
  rw [show 1+-Complex.sin w/Complex.sin φ=(Complex.sin φ-Complex.sin w)/Complex.sin φ by
    field_simp [hs]; ring]
  exact div_ne_zero hgap hs

theorem occupancyInverseV_angular_regular (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε τ σ υ θ : ℝ,
      0<ε → ε<ε₀ → 0≤τ → 0≤σ → 0≤υ → θ∈Icc (-Real.pi-B.delta) B.delta →
      AngularInverseRegular (preferredRadialTrace d ε) (preferredBumpAngle B.m B.p τ σ υ θ) := by
  obtain ⟨ε₀,hε₀,hm⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (by linarith [B.delta_alpha,d.alpha_pos])
  refine ⟨ε₀,hε₀,?_⟩
  intro ε τ σ υ θ hε hεr hτ hσ hυ hθ
  obtain ⟨hS,_,hSδ⟩ := hm ε hε hεr
  apply angularInverseRegular_of_upper _ _ B.delta B.delta_pos
    (by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]) hS hSδ
  · simpa [preferredBumpAngle] using hθ.1
  · simpa [preferredBumpAngle] using hθ.2
  · exact preferredBumpW_im_pos d B hε hτ hσ hυ θ

theorem angularInverseSlopeDerivative_continuousAt {S w : ℂ}
    (h : AngularInverseRegular S w) :
    ContinuousAt (fun z : ℂ × ℂ => angularInverseSlopeDerivative z.1 z.2) (S,w) := by
  have hi : ContinuousAt (fun z : ℂ × ℂ => z.1-Complex.cos z.2) (S,w) := by fun_prop
  have hp : ContinuousAt (fun z : ℂ × ℂ => preferredArccos (z.1-Complex.cos z.2)) (S,w) :=
    ContinuousAt.comp (f := fun z : ℂ × ℂ => z.1-Complex.cos z.2) (g := preferredArccos)
      h.1.continuousAt hi
  have hs := Complex.continuous_sin.continuousAt.comp hp
  have hb : ContinuousAt (fun z : ℂ × ℂ => 1+preferredPhaseSlope z.1 z.2) (S,w) :=
    continuousAt_const.add ((by fun_prop : ContinuousAt (fun z : ℂ × ℂ => -Complex.sin z.2) (S,w)).div hs h.2.2.2.2.1)
  have hq : ContinuousAt (fun z : ℂ × ℂ => preferredPhaseCurvature z.1 z.2) (S,w) :=
    (by fun_prop : ContinuousAt (fun z : ℂ × ℂ => z.1*(1-z.1*Complex.cos z.2+(Complex.cos z.2)^2)) (S,w)).div
      (hs.pow 3) (pow_ne_zero 3 h.2.2.2.2.1)
  exact hq.div (hb.pow 2) (pow_ne_zero 2 h.2.2.2.2.2)

theorem occupancyInverseV_deriv_continuousAt (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ σ υ θ : ℝ}
    (h : AngularInverseRegular (preferredRadialTrace d ε) (preferredBumpAngle B.m B.p τ σ υ θ)) :
    ContinuousAt (deriv (occupancyInverseV d B.m B.p ε τ σ υ)) θ := by
  have hm := B.m_smooth
  have hp := B.smooth
  have hmc := hm.continuous
  have hpc := hp.continuous
  have hmap : ContinuousAt (fun x => (preferredRadialTrace d ε,preferredBumpAngle B.m B.p τ σ υ x)) θ := by
    dsimp [preferredBumpAngle]
    fun_prop
  have hreg := hmap.eventually h.eventually
  have heq : deriv (occupancyInverseV d B.m B.p ε τ σ υ) =ᶠ[𝓝 θ]
      compactInverseSlopeDerivative d B.m B.p (deriv B.m) (deriv B.p) ε τ σ υ := by
    filter_upwards [hreg] with x hx
    exact (occupancyInverseV_hasDerivAt d ((contDiff_infty_iff_deriv.mp hm).1 x).hasDerivAt
      ((contDiff_infty_iff_deriv.mp hp).1 x).hasDerivAt hx).deriv
  apply ContinuousAt.congr_of_eventuallyEq ?_ heq
  have ha : ContinuousAt (fun x => angularInverseSlopeDerivative (preferredRadialTrace d ε)
      (preferredBumpAngle B.m B.p τ σ υ x)) θ :=
    ContinuousAt.comp (f := fun x => (preferredRadialTrace d ε,preferredBumpAngle B.m B.p τ σ υ x))
      (g := fun z : ℂ × ℂ => angularInverseSlopeDerivative z.1 z.2)
      (angularInverseSlopeDerivative_continuousAt h) hmap
  have hb : ContinuousAt (preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ) θ := by
    have hmc := hm.continuous_deriv (by simp)
    have hpc := hp.continuous_deriv (by simp)
    unfold preferredBumpTangent
    fun_prop
  exact ha.mul hb

theorem occupancyInverseV_plateau (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ : ℝ) {u : ℝ} (hu : |u|<preferredBranchPlateauWidth d B) :
    occupancyInverseV d B.m B.p ε τ σ υ (-d.b+u)=sourceInverseV d ε (τ*σ) u := by
  unfold occupancyInverseV
  rw [preferred_actual_plateau_angle d B τ σ υ hu]
  rfl

theorem occupancyInverseV_branch_hasDerivAt (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ σ υ u : ℝ} (hu : |u|<preferredBranchPlateauWidth d B)
    (hd : HasDerivAt (sourceInverseV d ε (τ*σ)) (sourceInverseSlopeDerivative d ε (τ*σ) u) u) :
    HasDerivAt (occupancyInverseV d B.m B.p ε τ σ υ)
      (sourceInverseSlopeDerivative d ε (τ*σ) u) (-d.b+u) := by
  have heq : occupancyInverseV d B.m B.p ε τ σ υ =ᶠ[𝓝 (-d.b+u)]
      (fun x => sourceInverseV d ε (τ*σ) (x+d.b)) := by
    have hnear : ∀ᶠ x : ℝ in 𝓝 (-d.b+u), |x+d.b|<preferredBranchPlateauWidth d B :=
      (by fun_prop : ContinuousAt (fun x : ℝ => |x+d.b|) (-d.b+u)).eventually_lt continuousAt_const
        (by simpa using hu)
    filter_upwards [hnear] with x hx
    convert occupancyInverseV_plateau d B ε τ σ υ hx using 1
    congr 1
    ring
  have hi : HasDerivAt (fun x : ℝ => x+d.b) 1 (-d.b+u) := by
    simpa using (hasDerivAt_id (-d.b+u)).add_const d.b
  have hh := hd.scomp_of_eq (-d.b+u) hi (show u=(-d.b+u)+d.b by ring)
  simp only [one_smul] at hh
  exact hh.congr_of_eventuallyEq heq

end
end IsingBulk.HT22.Geometry
