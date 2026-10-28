import IsingBulk.HT22.Geometry.AngularSlopeCalculus
import IsingBulk.Preferred22.Coarea

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter Set IsingBulk.Preferred22

/-- Primitive regularity of the literal angular inverse, before any
occupancy curve is substituted. -/
def AngularInverseRegular (S w : ℂ) : Prop :=
  AnalyticAt ℂ preferredArccos (S-Complex.cos w) ∧
  Complex.cos ((w+preferredArccos (S-Complex.cos w))/2) ≠ 0 ∧
  0 < ((preferredArccos (S-Complex.cos w)-w)/2).re ∧
  ((preferredArccos (S-Complex.cos w)-w)/2).re < Real.pi ∧
  Complex.sin (preferredArccos (S-Complex.cos w)) ≠ 0 ∧
  1+preferredPhaseSlope S w ≠ 0

theorem angularInverseRegular_real (d : PreferredBranchData)
    {ρ δR θ : ℝ} (hρ : 0<ρ) (hδb : δR<d.b) (hδα : δR<d.alpha)
    (hθ : θ∈Icc (-d.b+ρ) δR) :
    AngularInverseRegular ((1+Real.cos d.b:ℝ):ℂ) (θ:ℂ) := by
  obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδb hθ
  let g := Real.arccos (1+Real.cos d.b-Real.cos θ)
  have hg0 : 0<g := Real.arccos_pos.mpr hW'
  have hgπ : g<Real.pi := Real.arccos_lt_pi.mpr hW
  have hcg : Real.cos g = 1+Real.cos d.b-Real.cos θ := Real.cos_arccos hW.le hW'.le
  have hθg : θ<g := by
    by_cases ht : θ<0
    · linarith
    have ht0 := le_of_not_gt ht
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi ht0
      (show d.alpha≤Real.pi by linarith [d.alpha_lt,Real.pi_pos]) (hθ.2.trans_lt hδα)
    by_contra hn
    have hgc := Real.cos_le_cos_of_nonneg_of_le_pi hg0.le
      (show θ≤Real.pi by linarith [hθ.2,d.alpha_lt,Real.pi_pos]) (le_of_not_gt hn)
    rw [hcg,d.angle_relation] at hgc
    linarith
  have he : preferredArccos (((1+Real.cos d.b:ℝ):ℂ)-Complex.cos (θ:ℂ)) = (g:ℂ) := by
    rw [← Complex.ofReal_cos,show ((1+Real.cos d.b:ℝ):ℂ)-(Real.cos θ:ℂ)=
      ((1+Real.cos d.b-Real.cos θ:ℝ):ℂ) by push_cast; rfl]
    exact preferredArccos_ofReal _ hW hW'
  have ha : AnalyticAt ℂ preferredArccos (((1+Real.cos d.b:ℝ):ℂ)-Complex.cos (θ:ℂ)) := by
    convert preferredArccos_analyticAt_real _ hW hW' using 1
    push_cast
    rfl
  have hc : Complex.cos (((θ:ℂ)+preferredArccos (((1+Real.cos d.b:ℝ):ℂ)-Complex.cos (θ:ℂ)))/2)≠0 := by
    intro hz
    have hh := Complex.cos_add_cos (θ:ℂ)
      (preferredArccos (((1+Real.cos d.b:ℝ):ℂ)-Complex.cos (θ:ℂ)))
    rw [hz,mul_zero,zero_mul,cos_preferredArccos] at hh
    have hh' : ((1+Real.cos d.b:ℝ):ℂ)=0 := by linear_combination hh
    have hp := (preferred_reference_trace_range d).1
    exact hp.ne' (Complex.ofReal_eq_zero.mp hh')
  have hs : Complex.sin ((g:ℝ):ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hg0 hgπ).ne'
  refine ⟨ha,hc,?_,?_,by simpa only [he] using hs,
    (angularInverseSlopeDerivative_real_positive d hρ hδb hδα hθ).2.2⟩
  · rw [he]
    simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.ofReal_re]
    linarith
  · rw [he]
    simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.ofReal_re]
    linarith [hθ.1,d.b_lt]

theorem AngularInverseRegular.eventually {S w : ℂ} (h : AngularInverseRegular S w) :
    ∀ᶠ z : ℂ × ℂ in 𝓝 (S,w), AngularInverseRegular z.1 z.2 := by
  have harg : ContinuousAt (fun z : ℂ × ℂ => z.1-Complex.cos z.2) (S,w) := by fun_prop
  have hφ : ContinuousAt (fun z : ℂ × ℂ => preferredArccos (z.1-Complex.cos z.2)) (S,w) :=
    ContinuousAt.comp (f := fun z : ℂ × ℂ => z.1-Complex.cos z.2)
      (g := preferredArccos) h.1.continuousAt harg
  have hc := Complex.continuous_cos.continuousAt.comp ((continuousAt_snd.add hφ).div_const 2)
  have hh := Complex.continuous_re.continuousAt.comp ((hφ.sub continuousAt_snd).div_const 2)
  have hs := Complex.continuous_sin.continuousAt.comp hφ
  have hsl : ContinuousAt (fun z : ℂ × ℂ => 1+preferredPhaseSlope z.1 z.2) (S,w) :=
    continuousAt_const.add ((by fun_prop : ContinuousAt
      (fun z : ℂ × ℂ => -Complex.sin z.2) (S,w)).div hs h.2.2.2.2.1)
  filter_upwards [harg.eventually h.1.eventually_analyticAt,hc.eventually_ne h.2.1,
    continuousAt_const.eventually_lt hh h.2.2.1,
    hh.eventually_lt continuousAt_const h.2.2.2.1,hs.eventually_ne h.2.2.2.2.1,
    hsl.eventually_ne h.2.2.2.2.2] with z ha hc hl hu hs hd
  exact ⟨ha,hc,hl,hu,hs,hd⟩

/-- Uniform primitive strip/analytic margins for every fixed occupancy,
including both endpoints 0 and 1. Constants are chosen before ε and τ. -/
theorem compact_angular_inverse_regular (d : PreferredBranchData)
    (m p : ℝ → ℝ) (hm : Continuous m) (hp : Continuous p)
    {ρ δR : ℝ} (hρ : 0<ρ) (hδb : δR<d.b) (hδα : δR<d.alpha) :
    ∃ r : ℝ, 0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → θ∈Icc (-d.b+ρ) δR → σ∈Icc 0 1 → υ∈Icc 0 1 →
      AngularInverseRegular (preferredRadialTrace d ε) (preferredBumpAngle m p τ σ υ θ) := by
  let K : Set (ℝ × ℝ × ℝ) := Icc (-d.b+ρ) δR ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hevent : ∀ᶠ x : ℝ × ℝ in 𝓝 (0,0), ∀ y∈K,
      AngularInverseRegular (preferredRadialTrace d x.1)
        (preferredBumpAngle m p x.2 y.2.1 y.2.2 y.1) := by
    apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).eventually_forall_of_forall_eventually
    intro y hy
    have hbase := angularInverseRegular_real d hρ hδb hδα hy.1
    have hmap : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        (preferredRadialTrace d z.1.1,preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1)) ((0,0),y) := by
      dsimp [preferredRadialTrace,preferredBumpAngle,IsingBulk.Branch.radialParameter]
      fun_prop (disch := simp [Complex.exp_ne_zero])
    have hh := hmap.eventually (by simpa [preferredRadialTrace_zero,preferredBumpAngle] using hbase.eventually)
    exact hh
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r,hr,?_⟩
  intro ε τ σ υ θ hε hτ hθ hσ hυ
  apply hball (y := (ε,τ)) ?_ (θ,σ,υ) ⟨hθ,hσ,hυ⟩
  change dist (ε,τ) (0:ℝ × ℝ)<r
  simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hε hτ

def occupancyInverseV (d : PreferredBranchData) (m p : ℝ → ℝ)
    (ε τ σ υ θ : ℝ) : ℂ :=
  inverseV (IsingBulk.Branch.radialParameter d.alpha ε)
    (sumCoordinate (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredBumpAngle m p τ σ υ θ))

theorem occupancyInverseV_hasDerivAt (d : PreferredBranchData)
    {m p m' p' : ℝ → ℝ} {ε τ σ υ θ : ℝ}
    (hm : HasDerivAt m (m' θ) θ) (hp : HasDerivAt p (p' θ) θ)
    (h : AngularInverseRegular (preferredRadialTrace d ε) (preferredBumpAngle m p τ σ υ θ)) :
    HasDerivAt (occupancyInverseV d m p ε τ σ υ)
      (compactInverseSlopeDerivative d m p m' p' ε τ σ υ θ) θ := by
  have hd := inverseV_along_angle_hasDerivAt
    (IsingBulk.Branch.radialParameter d.alpha ε) (preferredBumpAngle m p τ σ υ θ)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  have hb := preferredBumpAngle_hasDerivAt (τ:=τ) (σ:=σ) (υ:=υ) hm hp
  have hh := hd.scomp θ hb
  unfold occupancyInverseV
  simpa only [compactInverseSlopeDerivative,Function.comp_def,smul_eq_mul,
    preferredRadialTrace,temperatureTrace,mul_comm] using hh

end
end IsingBulk.HT22.Geometry
