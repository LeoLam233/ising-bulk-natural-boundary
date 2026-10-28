import IsingBulk.HT22.Geometry.SourceBranch

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter Set IsingBulk.Preferred22

def angularInverseSlopeDerivative (S w : ℂ) : ℂ :=
  preferredPhaseCurvature S w/(1+preferredPhaseSlope S w)^2

def compactInverseSlopeDerivative (d : PreferredBranchData) (m p m' p' : ℝ → ℝ)
    (ε τ σ υ θ : ℝ) : ℂ :=
  angularInverseSlopeDerivative (preferredRadialTrace d ε)
    (preferredBumpAngle m p τ σ υ θ)*preferredBumpTangent m' p' τ σ υ θ

/-- The positive-angle endpoint must precede α, unlike the wider coarea
interval: the regular inverse degenerates at the positive saddle α. -/
theorem real_inverse_source_denominator_pos (d : PreferredBranchData)
    {ρ δR θ : ℝ} (hρ : 0 < ρ) (hδb : δR < d.b) (hδα : δR < d.alpha)
    (hθ : θ ∈ Icc (-d.b+ρ) δR) :
    0 < Real.sin (Real.arccos (1+Real.cos d.b-Real.cos θ))-Real.sin θ := by
  obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδb hθ
  have hs : 0 < Real.sin (Real.arccos (1+Real.cos d.b-Real.cos θ)) :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hW') (Real.arccos_lt_pi.mpr hW)
  by_cases ht : θ ≤ 0
  · have hst := Real.sin_nonpos_of_nonpos_of_neg_pi_le ht
      (by linarith [hθ.1,d.b_lt])
    linarith
  · have ht0 : 0 < θ := lt_of_not_ge ht
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le
      (show d.alpha ≤ Real.pi by linarith [d.alpha_lt,Real.pi_pos]) (hθ.2.trans_lt hδα)
    have hS := (preferred_reference_trace_range d).1
    have hcc : Real.cos (Real.arccos (1+Real.cos d.b-Real.cos θ)) =
        1+Real.cos d.b-Real.cos θ := Real.cos_arccos hW.le hW'.le
    have hsφ := Real.sin_sq_add_cos_sq (Real.arccos (1+Real.cos d.b-Real.cos θ))
    rw [hcc] at hsφ
    have hsθ := Real.sin_sq_add_cos_sq θ
    have hdiff : 0 < (1+Real.cos d.b)*(2*Real.cos θ-(1+Real.cos d.b)) := by
      apply mul_pos hS
      rw [d.angle_relation]
      linarith
    nlinarith [sq_nonneg (Real.sin θ+Real.sin (Real.arccos (1+Real.cos d.b-Real.cos θ)))]

theorem angularInverseSlopeDerivative_real_positive (d : PreferredBranchData)
    {ρ δR θ : ℝ} (hρ : 0 < ρ) (hδb : δR < d.b) (hδα : δR < d.alpha)
    (hθ : θ ∈ Icc (-d.b+ρ) δR) :
    (angularInverseSlopeDerivative ((1+Real.cos d.b:ℝ):ℂ) (θ:ℂ)).im = 0 ∧
    0 < (angularInverseSlopeDerivative ((1+Real.cos d.b:ℝ):ℂ) (θ:ℂ)).re ∧
    1+preferredPhaseSlope ((1+Real.cos d.b:ℝ):ℂ) (θ:ℂ) ≠ 0 := by
  obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδb hθ
  obtain ⟨hS,hS'⟩ := preferred_reference_trace_range d
  obtain ⟨hA,hQ,hQlo⟩ := preferred_reference_curvature_lower hS hS' hW hW'
  let s := Real.sin (Real.arccos (1+Real.cos d.b-Real.cos θ))
  have hs : 0 < s :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hW') (Real.arccos_lt_pi.mpr hW)
  have hd := real_inverse_source_denominator_pos d hρ hδb hδα hθ
  have hb : 1+preferredPhaseSlope ((1+Real.cos d.b:ℝ):ℂ) (θ:ℂ) =
      ((1-Real.sin θ/s:ℝ):ℂ) := by
    unfold preferredPhaseSlope
    rw [← Complex.ofReal_cos, show ((1+Real.cos d.b:ℝ):ℂ)-(Real.cos θ:ℂ) =
      ((1+Real.cos d.b-Real.cos θ:ℝ):ℂ) by push_cast; rfl,
      preferredArccos_ofReal _ hW hW',← Complex.ofReal_sin,← Complex.ofReal_sin]
    dsimp only [s]
    push_cast
    ring
  have hbpos : 0 < 1-Real.sin θ/s := by
    rw [sub_pos, div_lt_one hs]
    exact sub_pos.mp hd
  have hnum : 0 < (1+Real.cos d.b)*
      (1-(1+Real.cos d.b)*Real.cos θ+(Real.cos θ)^2)/s^3 := by
    have htmp := hQlo
    rw [hQ,Complex.ofReal_re] at htmp
    exact hA.trans_le htmp
  have he : angularInverseSlopeDerivative ((1+Real.cos d.b:ℝ):ℂ) (θ:ℂ) =
      (((1+Real.cos d.b)*(1-(1+Real.cos d.b)*Real.cos θ+(Real.cos θ)^2)/s^3 /
        (1-Real.sin θ/s)^2:ℝ):ℂ) := by
    rw [angularInverseSlopeDerivative,hQ,hb]
    dsimp only [s]
    push_cast
    rfl
  rw [he,hb]
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_ne_zero]
  exact ⟨True.intro,div_pos hnum (sq_pos_of_pos hbpos),hbpos.ne'⟩

theorem compactInverseSlope_continuousAt_zero (d : PreferredBranchData)
    (m p m' p' : ℝ → ℝ) (hm : Continuous m) (hp : Continuous p)
    (hm' : Continuous m') (hp' : Continuous p')
    {ρ δR θ σ υ : ℝ} (hρ : 0 < ρ) (hδb : δR < d.b) (hδα : δR < d.alpha)
    (hθ : θ ∈ Icc (-d.b+ρ) δR) :
    ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      compactInverseSlopeDerivative d m p m' p'
        z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
  obtain ⟨hQ,hb,_⟩ := preferredCompact_source_continuousAt_zero d m p m' p'
    (fun _ => 0) (fun _ => 0) hm hp hm' hp' continuous_const continuous_const hρ hδb hθ
  have hden := (angularInverseSlopeDerivative_real_positive d hρ hδb hδα hθ).2.2
  have ha : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpTangent m' p' z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
    unfold preferredBumpTangent
    fun_prop
  apply (hQ.div ((hb.const_add 1).pow 2) ?_).mul ha
  simpa [preferredCompactSlope,preferredBumpAngle,preferredRadialTrace_zero] using
    pow_ne_zero 2 hden

/-- Compactness preserves a quantitative π/4 cone and positive projection
when the reference derivative is genuinely positive real. This lemma is
only topology; the next theorem supplies the actual dispersion reference. -/
theorem compact_positive_real_persistence
    (K : Set (ℝ × ℝ × ℝ)) (hK : IsCompact K)
    (F : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℂ)
    (hF : ∀ y ∈ K, ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0),y))
    (hbase : ∀ y ∈ K, (F (0,0) y).im=0 ∧ 0<(F (0,0) y).re) :
    ∃ a B r : ℝ, 0<a ∧ 0<B ∧ 0<r ∧ ∀ ε τ : ℝ,
      |ε|<r → |τ|<r → ∀ y ∈ K,
      (1/4:ℝ)*‖F (ε,τ) y‖ ≤ (covarianceDirection*F (ε,τ) y).re ∧
      a ≤ (covarianceDirection*F (ε,τ) y).re ∧ ‖F (ε,τ) y‖ ≤ B := by
  let P := fun x y => (covarianceDirection*F x y).re
  have hp (y) (hy : y∈K) : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => P z.1 z.2) ((0,0),y) :=
    Complex.continuous_re.continuousAt.comp ((hF y hy).const_mul covarianceDirection)
  have hpos (y) (hy : y∈K) : 0<P (0,0) y ∧ (1/4:ℝ)*‖F (0,0) y‖<P (0,0) y := by
    obtain ⟨him,hre⟩ := hbase y hy
    have hn : ‖F (0,0) y‖=(F (0,0) y).re := by
      have he : F (0,0) y=((F (0,0) y).re:ℂ) := Complex.ext rfl (by simpa using him)
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hre,Complex.ofReal_re]
    obtain ⟨hdir,_⟩ := covarianceDirection_components
    have hs : 1≤Real.sqrt 2 := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
      have := Real.sqrt_nonneg (2:ℝ)
      nlinarith
    dsimp [P]
    rw [Complex.mul_re,him,mul_zero,sub_zero,hdir]
    rw [hn]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs) hre.le]
  have hPc : ContinuousOn (P (0,0)) K := by
    intro y hy
    exact ((hp y hy).comp (by fun_prop : ContinuousAt
      (fun y : ℝ × ℝ × ℝ => (((0,0):ℝ × ℝ),y)) y)).continuousWithinAt
  obtain ⟨A,hA,hAlow⟩ := hK.exists_forall_le' hPc (fun y hy => (hpos y hy).1)
  have hNc : ContinuousOn (fun y => ‖F (0,0) y‖) K := by
    intro y hy
    exact (((hF y hy).norm).comp (by fun_prop : ContinuousAt
      (fun y : ℝ × ℝ × ℝ => (((0,0):ℝ × ℝ),y)) y)).continuousWithinAt
  obtain ⟨B₀,hB₀⟩ := hK.exists_bound_of_continuousOn hNc
  let B := max B₀ 0+1
  have hB : 0<B := by dsimp [B]; positivity
  have hevent : ∀ᶠ x in 𝓝 ((0,0):ℝ × ℝ), ∀ y∈K,
      (1/4:ℝ)*‖F x y‖ < P x y ∧ A/2<P x y ∧ ‖F x y‖<B := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have hn := (hF y hy).norm
    have hb : ‖F (0,0) y‖<B := by
      have hh := hB₀ y hy
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at hh
      exact hh.trans_lt (by dsimp [B]; have := le_max_left B₀ 0; linarith)
    exact ((hn.const_mul (1/4:ℝ)).eventually_lt (hp y hy) (hpos y hy).2).and
      ((continuousAt_const.eventually_lt (hp y hy) (by have := hAlow y hy; linarith)).and
        (hn.eventually_lt continuousAt_const hb))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨A/2,B,r,by positivity,hB,hr,?_⟩
  intro ε τ hε hτ y hy
  have hx : dist (ε,τ) ((0,0):ℝ × ℝ)<r := by
    change dist (ε,τ) (0:ℝ × ℝ)<r
    simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hε hτ
  obtain ⟨hc,ha,hn⟩ := hball hx y hy
  exact ⟨hc.le,ha.le,hn.le⟩

theorem compact_inverse_source_estimate (d : PreferredBranchData)
    (m p m' p' : ℝ → ℝ) (hm : Continuous m) (hp : Continuous p)
    (hm' : Continuous m') (hp' : Continuous p')
    {ρ δR : ℝ} (hρ : 0<ρ) (hδb : δR<d.b) (hδα : δR<d.alpha) :
    ∃ a B r : ℝ, 0<a ∧ 0<B ∧ 0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → θ∈Icc (-d.b+ρ) δR → σ∈Icc 0 1 → υ∈Icc 0 1 →
      (1/4:ℝ)*‖compactInverseSlopeDerivative d m p m' p' ε τ σ υ θ‖ ≤
        (covarianceDirection*compactInverseSlopeDerivative d m p m' p' ε τ σ υ θ).re ∧
      a ≤ (covarianceDirection*compactInverseSlopeDerivative d m p m' p' ε τ σ υ θ).re ∧
      ‖compactInverseSlopeDerivative d m p m' p' ε τ σ υ θ‖ ≤ B := by
  let K : Set (ℝ × ℝ × ℝ) := Icc (-d.b+ρ) δR ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  let F := fun x : ℝ × ℝ => fun y : ℝ × ℝ × ℝ =>
    compactInverseSlopeDerivative d m p m' p' x.1 x.2 y.2.1 y.2.2 y.1
  have hcont (y) (hy:y∈K) := compactInverseSlope_continuousAt_zero d m p m' p'
    hm hp hm' hp' (σ := y.2.1) (υ := y.2.2) hρ hδb hδα hy.1
  have hbase (y) (hy:y∈K) : (F (0,0) y).im=0 ∧ 0<(F (0,0) y).re := by
    have hb := angularInverseSlopeDerivative_real_positive d hρ hδb hδα hy.1
    simpa [F,compactInverseSlopeDerivative,preferredBumpAngle,preferredBumpTangent,
      preferredRadialTrace_zero] using And.intro hb.1 hb.2.1
  obtain ⟨a,B,r,ha,hB,hr,hbound⟩ := compact_positive_real_persistence K
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) F hcont hbase
  refine ⟨a,B,r,ha,hB,hr,?_⟩
  intro ε τ σ υ θ hε hτ hθ hσ hυ
  exact hbound ε τ hε hτ (θ,σ,υ) ⟨hθ,hσ,hυ⟩

end
end IsingBulk.HT22.Geometry
