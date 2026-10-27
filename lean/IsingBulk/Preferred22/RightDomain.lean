import IsingBulk.Preferred22.RegularExtensions
import IsingBulk.Preferred22.ContourLegality
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex

namespace IsingBulk.Preferred22
noncomputable section
open scoped Topology BigOperators

/-- The complete limiting right inverse interval has room before the
critical endpoints v=±2alpha. -/
theorem preferred_branch_lt_two_alpha (d : PreferredBranchData) : d.b < 2*d.alpha := by
  have hc : 0 < Real.cos d.alpha := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [d.alpha_pos,Real.pi_pos],d.alpha_lt⟩
  have hc' : Real.cos d.alpha < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0)
      (show d.alpha≤Real.pi by linarith [d.alpha_lt,Real.pi_pos]) d.alpha_pos
    simpa using h
  by_contra hn
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [d.alpha_pos]) d.b_lt.le (le_of_not_gt hn)
  rw [d.angle_relation,Real.cos_two_mul] at hh
  nlinarith [mul_pos hc (sub_pos.mpr hc')]

/-- The explicit real interval |v|<2alpha has the actual inverse
square-root and cosine margins, without a supplied branch-domain premise. -/
theorem preferred_real_inverse_margins (d : PreferredBranchData) (v : ℝ)
    (hv : |v| < 2*d.alpha) :
    0 < Real.cos (v/2) ∧ 0 < inverseDiscriminant (1+Real.cos d.b) v := by
  have hav : |v/2|<d.alpha := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have hxlo : -(Real.pi/2)<v/2 := by have := (abs_lt.mp hav).1; linarith [d.alpha_lt]
  have hxhi : v/2<Real.pi/2 := (abs_lt.mp hav).2.trans d.alpha_lt
  have hc := Real.cos_pos_of_mem_Ioo ⟨hxlo,hxhi⟩
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (v/2))
    (show d.alpha≤Real.pi by linarith [d.alpha_lt,Real.pi_pos]) hav
  rw [Real.cos_abs] at hlt
  refine ⟨hc,?_⟩
  unfold inverseDiscriminant
  rw [d.angle_relation]
  have ha : 0<Real.cos d.alpha := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [d.alpha_pos,Real.pi_pos],d.alpha_lt⟩
  nlinarith

/-- The real part of the actual complex first derivative is the exact
source slope; the proof compares genuine real restrictions of derivatives. -/
theorem complexRightInverse_deriv_re_ofReal (S v : ℝ) (hS : 0<S)
    (hc : 0<Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    (deriv (complexRightInverse (S:ℂ)) (v:ℂ)).re=rightInverseSlope S v := by
  have ha := complexRightInverse_analyticAt_real S v hS hc hD
  have hsingle : AnalyticAt ℂ (complexRightInverse (S:ℂ)) (v:ℂ) :=
    AnalyticAt.comp (f := fun z : ℂ => ((S:ℂ),z))
      (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) ha
      (analyticAt_const.prod analyticAt_id)
  have hcontc : ContinuousAt (fun x : ℝ => Real.cos (x/2)) v := by fun_prop
  have hcontD : ContinuousAt (inverseDiscriminant S) v := by unfold inverseDiscriminant; fun_prop
  have hc' := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) v).eventually_lt hcontc hc
  have hD' := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) v).eventually_lt hcontD hD
  have he : (fun x : ℝ => (complexRightInverse (S:ℂ) x).re) =ᶠ[𝓝 v] rightInverse S := by
    filter_upwards [hc',hD'] with x hx hxD
    rw [complexRightInverse_ofReal S x hx hxD,Complex.ofReal_re]
  exact ((hsingle.differentiableAt.hasDerivAt.real_of_complex).congr_of_eventuallyEq he.symm).unique
    (rightInverse_hasDerivAt S v hc hD)

/-- Actual complex curvature has the real source value throughout the
limiting interval, so the positive margin transfers by continuity. -/
theorem complexRightInverse_second_re_ofReal (S v : ℝ) (hS : 0<S)
    (hc : 0<Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    (deriv (deriv (complexRightInverse (S:ℂ))) (v:ℂ)).re=rightInverseCurvature S v := by
  have ha := complexRightInverse_analyticAt_real S v hS hc hD
  have hsingle : AnalyticAt ℂ (complexRightInverse (S:ℂ)) (v:ℂ) :=
    AnalyticAt.comp (f := fun z : ℂ => ((S:ℂ),z))
      (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) ha
      (analyticAt_const.prod analyticAt_id)
  have hcontc : ContinuousAt (fun x : ℝ => Real.cos (x/2)) v := by fun_prop
  have hcontD : ContinuousAt (inverseDiscriminant S) v := by unfold inverseDiscriminant; fun_prop
  have hc' := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) v).eventually_lt hcontc hc
  have hD' := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) v).eventually_lt hcontD hD
  have he : (fun x : ℝ => (deriv (complexRightInverse (S:ℂ)) x).re) =ᶠ[𝓝 v] rightInverseSlope S := by
    filter_upwards [hc',hD'] with x hx hxD
    exact complexRightInverse_deriv_re_ofReal S x hS hx hxD
  exact ((hsingle.deriv.differentiableAt.hasDerivAt.real_of_complex).congr_of_eventuallyEq he.symm).unique
    (rightInverseSlope_hasDerivAt S v hc hD)

/-- The actual complex right curvature has the source's uniform S/8
margin on every closed interior limiting v interval. -/
theorem preferred_real_complex_curvature_margin (d : PreferredBranchData) (v : ℝ)
    (hv : |v|<2*d.alpha) :
    (1+Real.cos d.b)/8 ≤
      (deriv (deriv (complexRightInverse (((1+Real.cos d.b:ℝ):ℂ)))) (v:ℂ)).re := by
  obtain ⟨hc,hD⟩ := preferred_real_inverse_margins d v hv
  rw [complexRightInverse_second_re_ofReal _ v (preferred_reference_trace_range d).1 hc hD,
    ← rightInverse_second_deriv _ v hc hD]
  exact rightInverse_uniform_curvature _ v (preferred_reference_trace_range d).1 hc hD

/-- Exact real limiting source inverse, expressed in the actual moving q
coordinate rather than an auxiliary real inverse function. -/
theorem preferredMovingInverse_reference_real (d : PreferredBranchData) (v : ℝ)
    (hv : |v|<2*d.alpha) :
    preferredMovingInverse (preferredSelectedPoint d) ((v+d.b:ℝ):ℂ) =
      ((rightInverse (1+Real.cos d.b) v:ℝ):ℂ) := by
  obtain ⟨hc,hD⟩ := preferred_real_inverse_margins d v hv
  unfold preferredMovingInverse traceMovingInverse
  rw [temperatureTrace_preferredSelectedPoint,traceMovingBranch_reference]
  rw [show ((v+d.b:ℝ):ℂ)+ -(d.b:ℂ)=(v:ℂ) by push_cast; ring]
  exact complexRightInverse_ofReal _ v hc hD

theorem preferredRegularPhase_reference_real (d : PreferredBranchData) (v : ℝ)
    (hv : |v|<2*d.alpha) :
    preferredRegularPhase (preferredSelectedPoint d) ((v+d.b:ℝ):ℂ) =
      ((v/2+Real.arccos ((1+Real.cos d.b)/(2*Real.cos (v/2))):ℝ):ℂ) := by
  unfold preferredRegularPhase
  rw [preferredMovingInverse_reference_real d v hv,preferredMovingBranch_reference]
  unfold rightInverse
  push_cast
  ring

theorem preferredMovingInverse_reference_analytic (d : PreferredBranchData) (v : ℝ)
    (hv : |v|<2*d.alpha) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (preferredSelectedPoint d,((v+d.b:ℝ):ℂ)) := by
  obtain ⟨hc,hD⟩ := preferred_real_inverse_margins d v hv
  have hraw := complexRightInverse_analyticAt_real _ v (preferred_reference_trace_range d).1 hc hD
  have hS : AnalyticAt ℂ temperatureTrace (preferredSelectedPoint d) :=
    analyticAt_id.add (analyticAt_id.inv (preferredSelectedPoint_ne_zero d))
  have hSF := AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := temperatureTrace) hS
    (analyticAt_fst (p := (preferredSelectedPoint d,((v+d.b:ℝ):ℂ))))
  have hBF := AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch)
    (preferredMovingBranch_analyticAt_reference d)
    (analyticAt_fst (p := (preferredSelectedPoint d,((v+d.b:ℝ):ℂ))))
  exact hraw.comp_of_eq (hSF.prod (analyticAt_snd.add hBF)) (by
    apply Prod.ext
    · exact temperatureTrace_preferredSelectedPoint d
    · change ((v+d.b:ℝ):ℂ)+preferredMovingBranch (preferredSelectedPoint d)=(v:ℂ)
      rw [preferredMovingBranch_reference]
      push_cast
      ring)

/-- A compact convex real interval can be thickened once for all pairs,
while keeping a common complex parameter neighborhood. This is the finite
cover step used for the actual inverse and patched kernel below. -/
theorem preferred_compact_convex_product_tube (s₀ : ℂ) (K : Set ℂ)
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (G : Set (ℂ × ℂ × ℂ)) (hG : IsOpen G)
    (hbase : ∀ q∈K, ∀ r∈K, (s₀,q,r)∈G) :
    ∃ D : Set ℂ, ∃ ρ : ℝ, 0<ρ ∧ IsCompact D ∧ Convex ℝ D ∧ K⊆interior D ∧
      ∀ s q r : ℂ, ‖s-s₀‖<ρ → q∈D → r∈D → (s,q,r)∈G := by
  let L : Set (ℂ × ℂ × ℂ) := {s₀} ×ˢ (K ×ˢ K)
  have hL : IsCompact L := isCompact_singleton.prod (hK.prod hK)
  have hLG : L⊆G := by
    intro z hz
    rcases hz with ⟨hs,hq,hr⟩
    have hs' : z.1=s₀ := hs
    rw [← Prod.eta z,hs']
    exact hbase _ hq _ hr
  obtain ⟨δ,hδ,htube⟩ := hL.exists_thickening_subset_open hG hLG
  let ρ := δ/4
  let D := Metric.cthickening ρ K
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  refine ⟨D,ρ,hρ,hK.cthickening,hconv.cthickening ρ,?_,?_⟩
  · exact (Metric.self_subset_thickening hρ K).trans (Metric.thickening_subset_interior_cthickening ρ K)
  · intro s q r hs hq hr
    have hsmall : ρ<δ/2 := by dsimp [ρ]; linarith
    have hq' : q∈Metric.thickening (δ/2) K :=
      Metric.cthickening_subset_thickening' (half_pos hδ) hsmall K hq
    have hr' : r∈Metric.thickening (δ/2) K :=
      Metric.cthickening_subset_thickening' (half_pos hδ) hsmall K hr
    obtain ⟨q₀,hq₀,hdq⟩ := Metric.mem_thickening_iff.mp hq'
    obtain ⟨r₀,hr₀,hdr⟩ := Metric.mem_thickening_iff.mp hr'
    apply htube
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(s₀,q₀,r₀),⟨rfl,hq₀,hr₀⟩,?_⟩
    have hds : dist s s₀<δ := by rw [dist_eq_norm]; exact hs.trans (by dsimp [ρ]; linarith)
    have hdq' : dist q q₀<δ := hdq.trans (by linarith)
    have hdr' : dist r r₀<δ := hdr.trans (by linarith)
    simpa only [Prod.dist_eq,max_lt_iff] using And.intro hds (And.intro hdq' hdr')

/-- The actual complex second q-derivative inherits the explicit S/8
margin on the entire limiting right interval, before any compactness step. -/
theorem preferredMovingInverse_second_reference_margin (d : PreferredBranchData) (v : ℝ)
    (hv : |v|<2*d.alpha) :
    (1+Real.cos d.b)/8 ≤
      (deriv (deriv (preferredMovingInverse (preferredSelectedPoint d))) ((v+d.b:ℝ):ℂ)).re := by
  let S : ℂ := (((1+Real.cos d.b:ℝ):ℂ))
  have hfun : preferredMovingInverse (preferredSelectedPoint d)=
      fun q => complexRightInverse S (q+ -(d.b:ℂ)) := by
    funext q
    unfold preferredMovingInverse traceMovingInverse
    rw [temperatureTrace_preferredSelectedPoint,traceMovingBranch_reference]
  have hderfun : deriv (preferredMovingInverse (preferredSelectedPoint d))=
      fun q => deriv (complexRightInverse S) (q+ -(d.b:ℂ)) := by
    funext q
    rw [hfun]
    exact deriv_comp_add_const _ _ _
  rw [hderfun,deriv_comp_add_const,
    show ((v+d.b:ℝ):ℂ)+ -(d.b:ℂ)=(v:ℂ) by push_cast; ring]
  exact preferred_real_complex_curvature_margin d v hv

/-- A genuine joint derivative representative of Uqq. -/
def preferredMovingCurvature (s q : ℂ) : ℂ :=
  fderiv ℂ (preferredParameterQJet 0) (s,q) (0,1)

theorem preferredMovingCurvature_analyticAt (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingCurvature z.1 z.2) (s,q) := by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1):ℂ × ℂ)).analyticAt _).comp
    (preferredParameterQJet_analyticAt 0 (s,q) hU).fderiv

theorem preferredMovingCurvature_eq_deriv (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    preferredMovingCurvature s q=deriv (deriv (preferredMovingInverse s)) q := by
  have hJ := preferredParameterQJet_analyticAt 0 (s,q) hU
  have hd := hJ.differentiableAt.hasFDerivAt.comp_hasDerivAt q
    ((hasDerivAt_const q s).prodMk (hasDerivAt_id q))
  have ht : Filter.Tendsto (fun v : ℂ => (s,v)) (𝓝 q) (𝓝 (s,q)) :=
    (show Continuous (fun v : ℂ => (s,v)) by fun_prop).tendsto q
  have he : (fun v => preferredParameterQJet 0 (s,v)) =ᶠ[𝓝 q] deriv (preferredMovingInverse s) := by
    filter_upwards [ht.eventually hU.eventually_analyticAt] with v hv
    simpa only [iteratedDeriv_zero] using preferredParameterQJet_eq_iteratedDeriv 0 s v hv
  calc
    _ = deriv (fun v => preferredParameterQJet 0 (s,v)) q := by
      simpa only [preferredMovingCurvature,Function.comp_def,id_eq] using hd.deriv.symm
    _ = _ := he.deriv_eq

/-- The simultaneous analyticity and positive-real-curvature locus is open.
The curvature is the actual Uqq, represented by a genuine joint derivative. -/
theorem preferredMovingGood_isOpen (c : ℝ) :
    IsOpen {z : ℂ × ℂ | AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) z ∧
      c<(preferredMovingCurvature z.1 z.2).re} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hcont := Complex.continuous_re.continuousAt.comp
    (preferredMovingCurvature_analyticAt z.1 z.2 hz.1).continuousAt
  exact hz.1.eventually_analyticAt.and
    ((continuousAt_const : ContinuousAt (fun _ : ℂ × ℂ => c) z).eventually_lt hcont hz.2)

/-- Source-specific compact convex domain with a uniform actual Uqq
margin. The real interval is widened beyond both branch endpoints before
choosing the complex neighborhood; actual contour-image containment is
proved separately from the source coordinate scale and compact remainder. -/
theorem preferred_exists_uniform_right_domain (d : PreferredBranchData) :
    ∃ V ρ c : ℝ, ∃ D : Set ℂ,
      d.b<V ∧ V<2*d.alpha ∧ 0<ρ ∧ 0<c ∧ IsCompact D ∧ Convex ℝ D ∧
      0∈interior D ∧
      (∀ v : ℝ, |v|≤V → ((v+d.b:ℝ):ℂ)∈interior D) ∧
      (∀ s q : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D →
        AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) ∧
        c≤(deriv (deriv (preferredMovingInverse s)) q).re) := by
  let V := (d.b+2*d.alpha)/2
  have hV : d.b<V := by dsimp [V]; linarith [preferred_branch_lt_two_alpha d]
  have hV' : V<2*d.alpha := by dsimp [V]; linarith [preferred_branch_lt_two_alpha d]
  let K : Set ℂ := Complex.ofReal '' Set.Icc (d.b-V) (d.b+V)
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hconv : Convex ℝ K := (convex_Icc _ _).linear_image Complex.ofRealCLM.toLinearMap
  have hzero : (0:ℂ)∈K := ⟨0,⟨by linarith,by linarith [d.b_pos]⟩,by simp⟩
  let c := (1+Real.cos d.b)/16
  have hc : 0<c := by dsimp [c]; exact div_pos (preferred_reference_trace_range d).1 (by norm_num)
  let Good : Set (ℂ × ℂ) := {z | AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) z ∧
    c<(preferredMovingCurvature z.1 z.2).re}
  have hopen : IsOpen Good := preferredMovingGood_isOpen c
  have hbase (q : ℂ) (hq : q∈K) : (preferredSelectedPoint d,q)∈Good := by
    obtain ⟨x,hx,rfl⟩ := hq
    have hv : |x-d.b|<2*d.alpha := by
      have hh : |x-d.b|≤V := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
      exact hh.trans_lt hV'
    have hqeq : (((x-d.b)+d.b:ℝ):ℂ)=(x:ℂ) := by congr 1; ring
    have ha := preferredMovingInverse_reference_analytic d (x-d.b) hv
    rw [hqeq] at ha
    refine ⟨ha,?_⟩
    rw [preferredMovingCurvature_eq_deriv _ _ ha]
    have hh := preferredMovingInverse_second_reference_margin d (x-d.b) hv
    rw [hqeq] at hh
    dsimp [c]
    linarith [(preferred_reference_trace_range d).1]
  let G : Set (ℂ × ℂ × ℂ) :=
    (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) ⁻¹' Good ∩
    (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) ⁻¹' Good
  have hG : IsOpen G := (hopen.preimage (by fun_prop)).inter (hopen.preimage (by fun_prop))
  obtain ⟨D,ρ,hρ,hDc,hDv,hKD,hDgood⟩ := preferred_compact_convex_product_tube
    (preferredSelectedPoint d) K hK hconv G hG (fun q hq r hr => ⟨hbase q hq,hbase r hr⟩)
  refine ⟨V,ρ,c,D,hV,hV',hρ,hc,hDc,hDv,hKD hzero,?_,?_⟩
  · intro v hv
    apply hKD
    refine ⟨v+d.b,?_,rfl⟩
    obtain ⟨hl,hu⟩ := abs_le.mp hv
    constructor <;> linarith
  · intro s q hs hq
    have hh := (hDgood s q 0 hs hq (interior_subset (hKD hzero))).1
    refine ⟨hh.1,?_⟩
    rw [← preferredMovingCurvature_eq_deriv s q hh.1]
    exact hh.2.le

/-- Joint regular phase analyticity follows from the genuine moving inverse
and the actual moving center, at an arbitrary point of the right domain. -/
theorem preferredRegularPhase_analyticAt (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hB : AnalyticAt ℂ preferredMovingBranch s) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2) (s,q) := by
  exact (analyticAt_snd.sub hU).add
    (AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch) hB analyticAt_fst)

def preferredOneBodyGap (s q : ℂ) : ℂ :=
  Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q)

def preferredKernelExtensionDenominator (s q r : ℂ) : ℂ :=
  Complex.sin ((preferredRegularPhase s q+preferredRegularPhase s r)/2)^2+
    Complex.sin ((preferredMovingInverse s q+preferredMovingInverse s r)/2)^2

theorem preferredOneBodyGap_analyticAt (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hB : AnalyticAt ℂ preferredMovingBranch s) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredOneBodyGap z.1 z.2) (s,q) := by
  exact (Complex.analyticAt_sin.comp (preferredRegularPhase_analyticAt s q hU hB)).sub
    (Complex.analyticAt_sin.comp hU)

theorem preferredOneBodyExtension_analyticAt (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hB : AnalyticAt ℂ preferredMovingBranch s) (hg : preferredOneBodyGap s q ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (s,q) := by
  exact (analyticAt_const.mul (preferredOneBodyGap_analyticAt s q hU hB)).inv
    (mul_ne_zero Complex.I_ne_zero hg)

theorem preferredKernelExtensionDenominator_analyticAt (s q r : ℂ)
    (hq : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hr : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,r))
    (hB : AnalyticAt ℂ preferredMovingBranch s) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelExtensionDenominator z.1 z.2.1 z.2.2)
      (s,q,r) := by
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,q,r) :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hq' : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,q,r) :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hUq := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hq hp
  have hUr := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hr hq'
  have hφq := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
    (preferredRegularPhase_analyticAt s q hq hB) hp
  have hφr := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
    (preferredRegularPhase_analyticAt s r hr hB) hq'
  exact ((Complex.analyticAt_sin.comp ((hφq.add hφr).div_const (c := (2:ℂ)))).pow 2).add
    ((Complex.analyticAt_sin.comp ((hUq.add hUr).div_const (c := (2:ℂ)))).pow 2)

/-- The patched source kernel is jointly analytic on its actual nonzero
patch denominator. This formula includes both ordinary and branch charts. -/
theorem preferredKernelExtension_analyticAt (s q r : ℂ)
    (hq : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hr : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,r))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hD : preferredKernelExtensionDenominator s q r ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) (s,q,r) := by
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,q,r) :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hq' : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,q,r) :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hUq := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hq hp
  have hUr := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hr hq'
  have hφq := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
    (preferredRegularPhase_analyticAt s q hq hB) hp
  have hφr := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
    (preferredRegularPhase_analyticAt s r hr hB) hq'
  have hnum := (((show AnalyticAt ℂ (fun _ : ℂ × ℂ × ℂ => -Complex.I) (s,q,r) from analyticAt_const).mul (Complex.analyticAt_sin.comp
      ((hUq.sub hUr).div_const (c := (2:ℂ))))).mul
      (Complex.analyticAt_sin.comp ((hφq.add hφr).div_const (c := (2:ℂ))))).add
    (((show AnalyticAt ℂ (fun _ : ℂ × ℂ × ℂ => Complex.I) (s,q,r) from analyticAt_const).mul (Complex.analyticAt_sin.comp
      ((hφq.sub hφr).div_const (c := (2:ℂ))))).mul
      (Complex.analyticAt_sin.comp ((hUq.add hUr).div_const (c := (2:ℂ)))))
  exact hnum.div (preferredKernelExtensionDenominator_analyticAt s q r hq hr hB) hD

/-- The half-difference in the explicit real inverse stays strictly between
zero and pi/2 on the entire limiting right interval. -/
theorem preferred_real_half_difference (d : PreferredBranchData) (v : ℝ)
    (hv : |v| < 2*d.alpha) :
    0 < Real.arccos ((1+Real.cos d.b)/(2*Real.cos (v/2))) ∧
      Real.arccos ((1+Real.cos d.b)/(2*Real.cos (v/2))) < Real.pi/2 := by
  obtain ⟨hc,hD⟩ := preferred_real_inverse_margins d v hv
  have hS := (preferred_reference_trace_range d).1
  have hlt : 1+Real.cos d.b < 2*Real.cos (v/2) := by
    dsimp [inverseDiscriminant] at hD
    nlinarith
  exact ⟨Real.arccos_pos.mpr ((div_lt_one (by positivity)).mpr hlt),
    Real.arccos_lt_pi_div_two.mpr (div_pos hS (by positivity))⟩

/-- The one-body gap is nonzero throughout the full limiting right interval,
including the branch coordinate q=0. -/
theorem preferredOneBodyGap_reference_ne_zero (d : PreferredBranchData) (v : ℝ)
    (hv : |v| < 2*d.alpha) :
    preferredOneBodyGap (preferredSelectedPoint d) ((v+d.b:ℝ):ℂ) ≠ 0 := by
  obtain ⟨hc,_⟩ := preferred_real_inverse_margins d v hv
  obtain ⟨ha,ha'⟩ := preferred_real_half_difference d v hv
  let a := Real.arccos ((1+Real.cos d.b)/(2*Real.cos (v/2)))
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hp : 0 < Real.sin (v/2+a)-Real.sin (v/2-a) := by
    rw [Real.sin_add,Real.sin_sub]
    nlinarith [mul_pos hc hsa]
  unfold preferredOneBodyGap
  rw [preferredRegularPhase_reference_real d v hv,preferredMovingInverse_reference_real d v hv]
  unfold rightInverse
  rw [← Complex.ofReal_sin,← Complex.ofReal_sin,← Complex.ofReal_sub]
  exact_mod_cast hp.ne'

/-- The patched pair denominator is nonzero on the full real compact base,
including every pair collision and the simultaneous moving branch. -/
theorem preferredKernelExtensionDenominator_reference_ne_zero
    (d : PreferredBranchData) (v w : ℝ) (hv : |v| < 2*d.alpha) (hw : |w| < 2*d.alpha) :
    preferredKernelExtensionDenominator (preferredSelectedPoint d)
      ((v+d.b:ℝ):ℂ) ((w+d.b:ℝ):ℂ) ≠ 0 := by
  obtain ⟨ha,ha'⟩ := preferred_real_half_difference d v hv
  obtain ⟨hb,hb'⟩ := preferred_real_half_difference d w hw
  have hp := preferred_real_kernel_denominator_pos (v/2) (w/2) _ _ ha hb ha' hb'
  unfold preferredKernelExtensionDenominator
  rw [preferredRegularPhase_reference_real d v hv,preferredRegularPhase_reference_real d w hw,
    preferredMovingInverse_reference_real d v hv,preferredMovingInverse_reference_real d w hw]
  unfold rightInverse
  have hreal : 0 <
      Real.sin (((v/2+Real.arccos ((1+Real.cos d.b)/(2*Real.cos (v/2))))+
        (w/2+Real.arccos ((1+Real.cos d.b)/(2*Real.cos (w/2)))))/2)^2+
      Real.sin (((v/2-Real.arccos ((1+Real.cos d.b)/(2*Real.cos (v/2))))+
        (w/2-Real.arccos ((1+Real.cos d.b)/(2*Real.cos (w/2)))))/2)^2 := by
    convert! hp using 1
    ring_nf
  exact_mod_cast hreal.ne'

/-- The simultaneous source regularity conditions. Every field names the
literal inverse, curvature, or cancelled denominator, and the next theorem
constructs this locus uniformly from the selected root. -/
def PreferredRightRegularPoint (c : ℝ) (s q r : ℂ) : Prop :=
  AnalyticAt ℂ preferredMovingBranch s ∧
  AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) ∧
  AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,r) ∧
  c < (preferredMovingCurvature s q).re ∧ c < (preferredMovingCurvature s r).re ∧
  Complex.cos ((q+preferredMovingBranch s)/2) ≠ 0 ∧
  Complex.cos ((r+preferredMovingBranch s)/2) ≠ 0 ∧
  preferredOneBodyGap s q ≠ 0 ∧ preferredOneBodyGap s r ≠ 0 ∧
  preferredKernelExtensionDenominator s q r ≠ 0

theorem preferredRightRegularPoint_isOpen (c : ℝ) :
    IsOpen {z : ℂ × ℂ × ℂ | PreferredRightRegularPoint c z.1 z.2.1 z.2.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases hz with ⟨hB,hq,hr,hcq,hcr,hcosq,hcosr,hgq,hgr,hden⟩
  have hπq : ContinuousAt (fun x : ℂ × ℂ × ℂ => (x.1,x.2.1)) z := by fun_prop
  have hπr : ContinuousAt (fun x : ℂ × ℂ × ℂ => (x.1,x.2.2)) z := by fun_prop
  have hBc : ContinuousAt (fun x : ℂ × ℂ × ℂ => preferredMovingBranch x.1) z :=
    hB.continuousAt.comp continuousAt_fst
  have hcq' : ContinuousAt (fun x : ℂ × ℂ × ℂ => (preferredMovingCurvature x.1 x.2.1).re) z :=
    ContinuousAt.comp (f := fun x : ℂ × ℂ × ℂ => (x.1,x.2.1))
      (g := fun x : ℂ × ℂ => (preferredMovingCurvature x.1 x.2).re)
      (Complex.continuous_re.continuousAt.comp
        (preferredMovingCurvature_analyticAt z.1 z.2.1 hq).continuousAt) hπq
  have hcr' : ContinuousAt (fun x : ℂ × ℂ × ℂ => (preferredMovingCurvature x.1 x.2.2).re) z :=
    ContinuousAt.comp (f := fun x : ℂ × ℂ × ℂ => (x.1,x.2.2))
      (g := fun x : ℂ × ℂ => (preferredMovingCurvature x.1 x.2).re)
      (Complex.continuous_re.continuousAt.comp
        (preferredMovingCurvature_analyticAt z.1 z.2.2 hr).continuousAt) hπr
  have hcosq' : ContinuousAt (fun x : ℂ × ℂ × ℂ =>
      Complex.cos ((x.2.1+preferredMovingBranch x.1)/2)) z := by fun_prop
  have hcosr' : ContinuousAt (fun x : ℂ × ℂ × ℂ =>
      Complex.cos ((x.2.2+preferredMovingBranch x.1)/2)) z := by fun_prop
  have hgq' : ContinuousAt (fun x : ℂ × ℂ × ℂ => preferredOneBodyGap x.1 x.2.1) z :=
    ContinuousAt.comp (f := fun x : ℂ × ℂ × ℂ => (x.1,x.2.1))
      (g := fun x : ℂ × ℂ => preferredOneBodyGap x.1 x.2)
      (preferredOneBodyGap_analyticAt z.1 z.2.1 hq hB).continuousAt hπq
  have hgr' : ContinuousAt (fun x : ℂ × ℂ × ℂ => preferredOneBodyGap x.1 x.2.2) z :=
    ContinuousAt.comp (f := fun x : ℂ × ℂ × ℂ => (x.1,x.2.2))
      (g := fun x : ℂ × ℂ => preferredOneBodyGap x.1 x.2)
      (preferredOneBodyGap_analyticAt z.1 z.2.2 hr hB).continuousAt hπr
  have hden' := (preferredKernelExtensionDenominator_analyticAt z.1 z.2.1 z.2.2 hq hr hB).continuousAt
  exact (continuousAt_fst.tendsto.eventually hB.eventually_analyticAt).and
    ((hπq.tendsto.eventually hq.eventually_analyticAt).and
    ((hπr.tendsto.eventually hr.eventually_analyticAt).and
    (((continuousAt_const : ContinuousAt (fun _ : ℂ × ℂ × ℂ => c) z).eventually_lt hcq' hcq).and
    (((continuousAt_const : ContinuousAt (fun _ : ℂ × ℂ × ℂ => c) z).eventually_lt hcr' hcr).and
    ((hcosq'.eventually_ne hcosq).and ((hcosr'.eventually_ne hcosr).and
    ((hgq'.eventually_ne hgq).and ((hgr'.eventually_ne hgr).and (hden'.eventually_ne hden)))))))))

theorem preferred_reference_coordinate_cos_ne_zero (d : PreferredBranchData) (v : ℝ)
    (hv : |v| < 2*d.alpha) :
    Complex.cos ((((v+d.b:ℝ):ℂ)+preferredMovingBranch (preferredSelectedPoint d))/2) ≠ 0 := by
  rw [preferredMovingBranch_reference,
    show (((v+d.b:ℝ):ℂ)+ -(d.b:ℂ))/2=((v/2:ℝ):ℂ) by push_cast; ring,
    ← Complex.ofReal_cos]
  exact_mod_cast (preferred_real_inverse_margins d v hv).1.ne'

/-- A single compact convex domain regularizes the inverse, the one-body
factor, and every pair kernel simultaneously over the whole right interval.
The parameter neighborhood and the domain are fixed before any jet order. -/
theorem preferred_exists_uniform_regular_domain (d : PreferredBranchData) :
    ∃ V ρ c : ℝ, ∃ D : Set ℂ,
      d.b < V ∧ V < 2*d.alpha ∧ 0 < ρ ∧ 0 < c ∧ IsCompact D ∧ Convex ℝ D ∧
      0 ∈ interior D ∧
      (∀ v : ℝ, |v| ≤ V → ((v+d.b:ℝ):ℂ) ∈ interior D) ∧
      (∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖ < ρ → q ∈ D → r ∈ D →
        PreferredRightRegularPoint c s q r) := by
  let V := (d.b+2*d.alpha)/2
  have hV : d.b < V := by dsimp [V]; linarith [preferred_branch_lt_two_alpha d]
  have hV' : V < 2*d.alpha := by dsimp [V]; linarith [preferred_branch_lt_two_alpha d]
  let K : Set ℂ := Complex.ofReal '' Set.Icc (d.b-V) (d.b+V)
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hconv : Convex ℝ K := (convex_Icc _ _).linear_image Complex.ofRealCLM.toLinearMap
  have hzero : (0:ℂ) ∈ K := ⟨0,⟨by linarith,by linarith [d.b_pos]⟩,by simp⟩
  let c := (1+Real.cos d.b)/16
  have hc : 0 < c := by dsimp [c]; exact div_pos (preferred_reference_trace_range d).1 (by norm_num)
  have hbase (q r : ℂ) (hq : q ∈ K) (hr : r ∈ K) :
      PreferredRightRegularPoint c (preferredSelectedPoint d) q r := by
    obtain ⟨x,hx,rfl⟩ := hq
    obtain ⟨y,hy,rfl⟩ := hr
    have hv : |x-d.b| < 2*d.alpha :=
      (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩ : |x-d.b| ≤ V).trans_lt hV'
    have hw : |y-d.b| < 2*d.alpha :=
      (abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩ : |y-d.b| ≤ V).trans_lt hV'
    have hxeq : (((x-d.b)+d.b:ℝ):ℂ)=(x:ℂ) := by congr 1; ring
    have hyeq : (((y-d.b)+d.b:ℝ):ℂ)=(y:ℂ) := by congr 1; ring
    have hUq := preferredMovingInverse_reference_analytic d (x-d.b) hv
    have hUr := preferredMovingInverse_reference_analytic d (y-d.b) hw
    rw [hxeq] at hUq
    rw [hyeq] at hUr
    refine ⟨preferredMovingBranch_analyticAt_reference d,hUq,hUr,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [preferredMovingCurvature_eq_deriv _ _ hUq]
      have hh := preferredMovingInverse_second_reference_margin d (x-d.b) hv
      rw [hxeq] at hh
      dsimp [c]
      linarith [(preferred_reference_trace_range d).1]
    · rw [preferredMovingCurvature_eq_deriv _ _ hUr]
      have hh := preferredMovingInverse_second_reference_margin d (y-d.b) hw
      rw [hyeq] at hh
      dsimp [c]
      linarith [(preferred_reference_trace_range d).1]
    · simpa only [hxeq] using preferred_reference_coordinate_cos_ne_zero d (x-d.b) hv
    · simpa only [hyeq] using preferred_reference_coordinate_cos_ne_zero d (y-d.b) hw
    · simpa only [hxeq] using preferredOneBodyGap_reference_ne_zero d (x-d.b) hv
    · simpa only [hyeq] using preferredOneBodyGap_reference_ne_zero d (y-d.b) hw
    · simpa only [hxeq,hyeq] using
        preferredKernelExtensionDenominator_reference_ne_zero d (x-d.b) (y-d.b) hv hw
  obtain ⟨D,ρ,hρ,hDc,hDv,hKD,hgood⟩ := preferred_compact_convex_product_tube
    (preferredSelectedPoint d) K hK hconv
    {z : ℂ × ℂ × ℂ | PreferredRightRegularPoint c z.1 z.2.1 z.2.2}
    (preferredRightRegularPoint_isOpen c) (fun q hq r hr => hbase q r hq hr)
  refine ⟨V,ρ,c,D,hV,hV',hρ,hc,hDc,hDv,hKD hzero,?_,hgood⟩
  intro v hv
  apply hKD
  refine ⟨v+d.b,?_,rfl⟩
  obtain ⟨hl,hu⟩ := abs_le.mp hv
  constructor <;> linarith

/-- The selected inverse cosine remains continuous at its branch endpoint.
This is the exact square-root continuity needed for a uniform source image. -/
theorem preferredArccos_continuousAt_one : ContinuousAt preferredArccos (1:ℂ) := by
  have hinner : ContinuousAt (fun z : ℂ => 1-z^2) 1 := by fun_prop
  have hsqrt : ContinuousAt (fun z : ℂ => Complex.sqrt (1-z^2)) 1 :=
    (Complex.continuousAt_sqrt (z := 0) (Or.inl (by norm_num))).comp_of_eq hinner (by norm_num)
  have hroot : ContinuousAt preferredCosineRoot 1 :=
    continuousAt_id.add (continuousAt_const.mul hsqrt)
  exact continuousAt_const.mul (hroot.clog (by
    simp [preferredCosineRoot,Complex.slitPlane]))

theorem preferredArccos_one : preferredArccos (1:ℂ)=0 := by
  simp [preferredArccos,preferredCosineRoot]

theorem preferredArccos_continuousAt_real_closed (a : ℝ) (ha : -1<a) (ha' : a≤1) :
    ContinuousAt preferredArccos (a:ℂ) := by
  rcases ha'.eq_or_lt with h | h
  · subst a
    simpa only [Complex.ofReal_one] using preferredArccos_continuousAt_one
  · exact (preferredArccos_analyticAt_real a ha h).continuousAt

theorem preferredArccos_ofReal_closed (a : ℝ) (ha : -1<a) (ha' : a≤1) :
    preferredArccos (a:ℂ)=(Real.arccos a:ℂ) := by
  rcases ha'.eq_or_lt with h | h
  · subst a
    simp [preferredArccos_one]
  · exact preferredArccos_ofReal a ha h

/-- Actual zero-radius right phase and coordinate bounds, including the
lower branch endpoint. -/
theorem preferred_right_limit_phase_bounds (d : PreferredBranchData) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (-d.b) 0) :
    -1 < 1+Real.cos d.b-Real.cos θ ∧ 1+Real.cos d.b-Real.cos θ ≤ 1 ∧
    0 ≤ Real.arccos (1+Real.cos d.b-Real.cos θ) ∧
      Real.arccos (1+Real.cos d.b-Real.cos θ) ≤ d.b := by
  have ha : |θ|≤d.b := abs_le.mpr ⟨hθ.1,by linarith [hθ.2,d.b_pos]⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) d.b_lt.le ha
  rw [Real.cos_abs] at hcos
  have hW : Real.cos d.b ≤ 1+Real.cos d.b-Real.cos θ := by linarith [Real.cos_le_one θ]
  have hφ := Real.arccos_le_arccos hW
  rw [Real.arccos_cos d.b_pos.le d.b_lt.le] at hφ
  exact ⟨by linarith [(preferred_reference_trace_range d).1],by linarith,
    Real.arccos_nonneg _,hφ⟩

/-- Scalar source coordinate with both genuine occupancies retained. -/
def preferredBumpCoordinate (d : PreferredBranchData) (p m : ℝ → ℝ)
    (ε τ σ υ θ : ℝ) : ℂ :=
  preferredArccos (preferredRadialTrace d ε-Complex.cos (preferredBumpAngle m p τ σ υ θ))+
    preferredBumpAngle m p τ σ υ θ-
      preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)

theorem preferredBumpCoordinate_zero (d : PreferredBranchData) (p m : ℝ → ℝ)
    (σ υ θ : ℝ) (hθ : θ ∈ Set.Icc (-d.b) 0) :
    preferredBumpCoordinate d p m 0 0 σ υ θ =
      ((Real.arccos (1+Real.cos d.b-Real.cos θ)+θ+d.b:ℝ):ℂ) := by
  obtain ⟨hW,hW',_,_⟩ := preferred_right_limit_phase_bounds d θ hθ
  unfold preferredBumpCoordinate
  rw [show IsingBulk.Branch.radialParameter d.alpha 0=preferredSelectedPoint d by rfl,
    preferredMovingBranch_reference,preferredRadialTrace_zero]
  simp only [preferredBumpAngle,Complex.ofReal_zero,mul_zero,zero_mul,sub_zero]
  rw [← Complex.ofReal_cos,
    show ((1+Real.cos d.b:ℝ):ℂ)-(Real.cos θ:ℂ)=((1+Real.cos d.b-Real.cos θ:ℝ):ℂ) by push_cast; rfl,
    preferredArccos_ofReal_closed _ hW hW']
  push_cast
  ring

theorem preferredBumpCoordinate_continuousAt_zero (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) (θ σ υ : ℝ) (hθ : θ ∈ Set.Icc (-d.b) 0) :
    ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpCoordinate d p m z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
  obtain ⟨hW,hW',_,_⟩ := preferred_right_limit_phase_bounds d θ hθ
  have hw : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
    unfold preferredBumpAngle
    fun_prop
  have harg : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredRadialTrace d z.1.1-Complex.cos (preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1))
        ((0,0),(θ,σ,υ)) := by
    unfold preferredRadialTrace IsingBulk.Branch.radialParameter
    fun_prop (disch := simp [Complex.exp_ne_zero])
  have harc := (preferredArccos_continuousAt_real_closed _ hW hW').comp_of_eq harg (by
    simp only [preferredRadialTrace_zero,preferredBumpAngle,Complex.ofReal_zero,mul_zero,zero_mul,sub_zero]
    rw [← Complex.ofReal_cos]
    push_cast
    rfl)
  have hparam : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      IsingBulk.Branch.radialParameter d.alpha z.1.1) ((0,0),(θ,σ,υ)) := by
    unfold IsingBulk.Branch.radialParameter
    fun_prop
  have hB := (preferredMovingBranch_analyticAt_reference d).continuousAt.comp_of_eq hparam (by rfl)
  exact (harc.add hw).sub hB

/-- Uniform actual scalar image containment on a right interval widened
on both sides, with the small parameters chosen before both occupancies. -/
theorem preferred_bump_coordinate_image (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) (D : Set ℂ)
    (hD : ∀ x : ℝ, 0≤x → x≤2*d.b → (x:ℂ) ∈ interior D) :
    ∃ r : ℝ, 0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → σ ∈ Set.Icc 0 1 → υ ∈ Set.Icc 0 1 →
      -d.b-r≤θ → θ≤r → preferredBumpCoordinate d p m ε τ σ υ θ ∈ interior D := by
  let K : Set (ℝ × ℝ × ℝ) := Set.Icc (-d.b) 0 ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  let F : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℂ := fun x y =>
    preferredBumpCoordinate d p m x.1 x.2.1 y.2.1 y.2.2 (y.1+x.2.2)
  have hbase (y : ℝ × ℝ × ℝ) (hy : y ∈ K) : F (0,0,0) y ∈ interior D := by
    dsimp [F]
    rw [add_zero,preferredBumpCoordinate_zero d p m _ _ _ hy.1]
    obtain ⟨_,_,hφ,hφ'⟩ := preferred_right_limit_phase_bounds d y.1 hy.1
    apply hD <;> linarith [hy.1.1,hy.1.2]
  have hcont (y : ℝ × ℝ × ℝ) (hy : y ∈ K) :
      ContinuousAt (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0,0),y) := by
    have hh := preferredBumpCoordinate_continuousAt_zero d p m hp hm y.1 y.2.1 y.2.2 hy.1
    let H : ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
      fun z => ((z.1.1,z.1.2.1),(z.2.1+z.1.2.2,z.2.2.1,z.2.2.2))
    have hH : ContinuousAt H ((0,0,0),y) := by dsimp [H]; fun_prop
    exact ContinuousAt.comp_of_eq (f := H)
      (g := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        preferredBumpCoordinate d p m z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1)
      hh hH (by simp [H])

  have hevent : ∀ᶠ x in 𝓝 ((0,0,0):ℝ × ℝ × ℝ), ∀ y ∈ K, F x y ∈ interior D := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    exact (hcont y hy).preimage_mem_nhds (isOpen_interior.mem_nhds (hbase y hy))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r/2,half_pos hr,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθL hθR
  have happly (θ₀ e : ℝ) (hθ₀ : θ₀ ∈ Set.Icc (-d.b) 0) (he : |e|<r)
      (heq : θ₀+e=θ) : preferredBumpCoordinate d p m ε τ σ υ θ ∈ interior D := by
    have hd : dist (ε,τ,e) ((0,0,0):ℝ × ℝ × ℝ)<r := by
      simpa only [Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] using
        And.intro (hε.trans (by linarith)) (And.intro (hτ.trans (by linarith)) he)
    have hh := hball hd (θ₀,σ,υ) ⟨hθ₀,hσ,hυ⟩
    simpa only [F,heq] using hh
  by_cases hlo : θ < -d.b
  · apply happly (-d.b) (θ+d.b) ⟨le_rfl,by linarith [d.b_pos]⟩ _ (by ring)
    rw [abs_of_neg (by linarith)]
    linarith
  · by_cases hhi : 0<θ
    · apply happly 0 θ ⟨by linarith [d.b_pos],le_rfl⟩ _ (by ring)
      rw [abs_of_pos hhi]
      linarith
    · exact happly θ 0 ⟨le_of_not_gt hlo,le_of_not_gt hhi⟩ (by simpa using hr) (by ring)

/-- Positive real curvature on the fixed convex inverse domain gives the
actual secant margin required by the collective pair quotients. -/
theorem preferred_slope_secant_re_lower (s : ℂ) (D : Set ℂ) (c : ℝ)
    (hD : Convex ℝ D)
    (hU : ∀ z ∈ D, DifferentiableAt ℂ (preferredSourceUQ s) z)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (preferredSourceUQ s) z).re)
    (q r : ℂ) (hq : q ∈ D) (hr : r ∈ D) (hqr : q ≠ r) :
    c ≤ ((preferredSourceUQ s q-preferredSourceUQ s r)/(q-r)).re := by
  let f : ℝ → ℝ := fun t =>
    ((preferredSourceUQ s (r+(t:ℂ)*(q-r))-preferredSourceUQ s r)/(q-r)).re
  have hqrz : q-r ≠ 0 := sub_ne_zero.mpr hqr
  have hmem (t : ℝ) (ht : t ∈ Set.Icc 0 1) : r+(t:ℂ)*(q-r) ∈ D := by
    simpa only [Complex.real_smul] using hD.add_smul_sub_mem hr hq ht
  have hder (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      HasDerivAt f (deriv (preferredSourceUQ s) (r+(t:ℂ)*(q-r))).re t := by
    have hz : HasDerivAt (fun z : ℂ => r+z*(q-r)) (q-r) (t:ℂ) := by
      convert! (hasDerivAt_const (t:ℂ) r).add ((hasDerivAt_id (t:ℂ)).mul_const (q-r)) using 1
      simp
    have hh := (((hU _ (hmem t ht)).hasDerivAt.comp (t:ℂ) hz).sub_const
      (preferredSourceUQ s r)).div_const (q-r)
    convert! hh.real_of_complex using 1
    congr 1
    field_simp
  have hc : ContinuousOn f (Set.Icc 0 1) := fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (interior (Set.Icc 0 1)) :=
    fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hb : ∀ t ∈ interior (Set.Icc 0 1), c ≤ deriv f t := by
    intro t ht
    rw [(hder t (interior_subset ht)).deriv]
    exact hcurv _ (hmem t (interior_subset ht))
  have hh := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv hc hd hb
    0 (by simp) 1 (by simp) (by norm_num)
  have hzero : f 0=0 := by simp [f]
  have hone : f 1=((preferredSourceUQ s q-preferredSourceUQ s r)/(q-r)).re := by
    simp [f]
  simpa only [hzero,hone,sub_zero,one_mul,mul_one] using hh

/-- Thus a collision of actual slopes is an actual coordinate collision;
the source algebra's compatibility hypothesis follows from P5 curvature. -/
theorem preferredSourceUQ_injectiveOn (s : ℂ) (D : Set ℂ) (c : ℝ) (hc : 0<c)
    (hD : Convex ℝ D)
    (hU : ∀ z ∈ D, DifferentiableAt ℂ (preferredSourceUQ s) z)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (preferredSourceUQ s) z).re) :
    Set.InjOn (preferredSourceUQ s) D := by
  intro q hq r hr hsame
  by_contra hqr
  have hh := preferred_slope_secant_re_lower s D c hD hU hcurv q r hq hr hqr
  rw [hsame,sub_self,zero_div,Complex.zero_re] at hh
  linarith

/-- The exact collective identities now follow from the actual curvature
condition, with no separately assumed slope-collision compatibility. -/
theorem preferredResidualCollective_constraints_of_curvature {N : ℕ}
    (s : ℂ) (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z ∈ D, DifferentiableAt ℂ (preferredSourceUQ s) z)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (preferredSourceUQ s) z).re)
    (q : Fin N → ℂ) (hq : ∀ i, q i ∈ D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (q i)) ≠ 0) :
    (∑ i, preferredResidualCollective s q i) = -(N:ℂ)*deriv preferredMovingBranch s ∧
    (∑ i, preferredSourceUQ s (q i)*preferredResidualCollective s q i) =
      -(∑ i, preferredSourceUDot s (q i)) := by
  apply preferredResidualCollective_constraints s q _ hR
  intro i j hij
  exact congrArg (preferredMovingInverse s)
    (preferredSourceUQ_injectiveOn s D c hc hD hU hcurv (hq i) (hq j) hij)

/-- The full real reference phase bound depends only on |theta|≤b. -/
theorem preferred_right_limit_phase_bounds_abs (d : PreferredBranchData) (θ : ℝ)
    (hθ : |θ|≤d.b) :
    -1 < 1+Real.cos d.b-Real.cos θ ∧ 1+Real.cos d.b-Real.cos θ ≤ 1 ∧
    0 ≤ Real.arccos (1+Real.cos d.b-Real.cos θ) ∧
      Real.arccos (1+Real.cos d.b-Real.cos θ) ≤ d.b := by
  have hh := preferred_right_limit_phase_bounds d (-|θ|)
    ⟨by linarith,neg_nonpos.mpr (abs_nonneg θ)⟩
  simpa only [Real.cos_neg,Real.cos_abs] using hh

theorem preferredBumpCoordinate_zero_abs (d : PreferredBranchData) (p m : ℝ → ℝ)
    (σ υ θ : ℝ) (hθ : |θ|≤d.b) :
    preferredBumpCoordinate d p m 0 0 σ υ θ =
      ((Real.arccos (1+Real.cos d.b-Real.cos θ)+θ+d.b:ℝ):ℂ) := by
  obtain ⟨hW,hW',_,_⟩ := preferred_right_limit_phase_bounds_abs d θ hθ
  unfold preferredBumpCoordinate
  rw [show IsingBulk.Branch.radialParameter d.alpha 0=preferredSelectedPoint d by rfl,
    preferredMovingBranch_reference,preferredRadialTrace_zero]
  simp only [preferredBumpAngle,Complex.ofReal_zero,mul_zero,zero_mul,sub_zero]
  rw [← Complex.ofReal_cos,
    show ((1+Real.cos d.b:ℝ):ℂ)-(Real.cos θ:ℂ)=((1+Real.cos d.b-Real.cos θ:ℝ):ℂ) by push_cast; rfl,
    preferredArccos_ofReal_closed _ hW hW']
  push_cast
  ring

theorem preferredBumpCoordinate_continuousAt_zero_abs (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) (θ σ υ : ℝ) (hθ : |θ|≤d.b) :
    ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpCoordinate d p m z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
  obtain ⟨hW,hW',_,_⟩ := preferred_right_limit_phase_bounds_abs d θ hθ
  have hw : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
    unfold preferredBumpAngle
    fun_prop
  have harg : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredRadialTrace d z.1.1-Complex.cos (preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1))
        ((0,0),(θ,σ,υ)) := by
    unfold preferredRadialTrace IsingBulk.Branch.radialParameter
    fun_prop (disch := simp [Complex.exp_ne_zero])
  have harc := (preferredArccos_continuousAt_real_closed _ hW hW').comp_of_eq harg (by
    simp only [preferredRadialTrace_zero,preferredBumpAngle,Complex.ofReal_zero,mul_zero,zero_mul,sub_zero]
    rw [← Complex.ofReal_cos]
    push_cast
    rfl)
  have hparam : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      IsingBulk.Branch.radialParameter d.alpha z.1.1) ((0,0),(θ,σ,υ)) := by
    unfold IsingBulk.Branch.radialParameter
    fun_prop
  have hB := (preferredMovingBranch_analyticAt_reference d).continuousAt.comp_of_eq hparam (by rfl)
  exact (harc.add hw).sub hB

/-- Uniform actual scalar image containment on a right interval widened
on both sides, with the small parameters chosen before both occupancies. -/
theorem preferred_bump_coordinate_image_fixed (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) (δR : ℝ) (hδR : 0≤δR) (hδRb : δR≤d.b) (D : Set ℂ)
    (hD : ∀ x : ℝ, 0≤x → x≤2*d.b+δR → (x:ℂ) ∈ interior D) :
    ∃ r : ℝ, 0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → σ ∈ Set.Icc 0 1 → υ ∈ Set.Icc 0 1 →
      -d.b-r≤θ → θ≤δR → preferredBumpCoordinate d p m ε τ σ υ θ ∈ interior D := by
  let K : Set (ℝ × ℝ × ℝ) := Set.Icc (-d.b) δR ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  let F : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℂ := fun x y =>
    preferredBumpCoordinate d p m x.1 x.2.1 y.2.1 y.2.2 (y.1+x.2.2)
  have hbase (y : ℝ × ℝ × ℝ) (hy : y ∈ K) : F (0,0,0) y ∈ interior D := by
    dsimp [F]
    have habs : |y.1|≤d.b := abs_le.mpr ⟨hy.1.1,hy.1.2.trans hδRb⟩
    rw [add_zero,preferredBumpCoordinate_zero_abs d p m _ _ _ habs]
    obtain ⟨_,_,hφ,hφ'⟩ := preferred_right_limit_phase_bounds_abs d y.1 habs
    apply hD <;> linarith [hy.1.1,hy.1.2]
  have hcont (y : ℝ × ℝ × ℝ) (hy : y ∈ K) :
      ContinuousAt (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0,0),y) := by
    have hh := preferredBumpCoordinate_continuousAt_zero_abs d p m hp hm y.1 y.2.1 y.2.2
      (abs_le.mpr ⟨hy.1.1,hy.1.2.trans hδRb⟩)
    let H : ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
      fun z => ((z.1.1,z.1.2.1),(z.2.1+z.1.2.2,z.2.2.1,z.2.2.2))
    have hH : ContinuousAt H ((0,0,0),y) := by dsimp [H]; fun_prop
    exact ContinuousAt.comp_of_eq (f := H)
      (g := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        preferredBumpCoordinate d p m z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1)
      hh hH (by simp [H])

  have hevent : ∀ᶠ x in 𝓝 ((0,0,0):ℝ × ℝ × ℝ), ∀ y ∈ K, F x y ∈ interior D := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    exact (hcont y hy).preimage_mem_nhds (isOpen_interior.mem_nhds (hbase y hy))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r/2,half_pos hr,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθL hθR
  have happly (θ₀ e : ℝ) (hθ₀ : θ₀ ∈ Set.Icc (-d.b) δR) (he : |e|<r)
      (heq : θ₀+e=θ) : preferredBumpCoordinate d p m ε τ σ υ θ ∈ interior D := by
    have hd : dist (ε,τ,e) ((0,0,0):ℝ × ℝ × ℝ)<r := by
      simpa only [Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] using
        And.intro (hε.trans (by linarith)) (And.intro (hτ.trans (by linarith)) he)
    have hh := hball hd (θ₀,σ,υ) ⟨hθ₀,hσ,hυ⟩
    simpa only [F,heq] using hh
  by_cases hlo : θ < -d.b
  · apply happly (-d.b) (θ+d.b) ⟨le_rfl,by linarith [d.b_pos]⟩ _ (by ring)
    rw [abs_of_neg (by linarith)]
    linarith
  · exact happly θ 0 ⟨le_of_not_gt hlo,hθR⟩ (by simpa using hr) (by ring)

/-- Every fixed joint jet of the source regular amplitudes is bounded on
one parameter tube and one fixed compact right domain, uniformly before
radial limits or particle counts are introduced. -/
theorem preferred_regular_domain_all_jets (d : PreferredBranchData) (ρ c : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D) (hzero : (0:ℂ)∈D)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
      (∀ s q : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D →
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (s,q)‖≤C) ∧
      (∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D → r∈D →
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) (s,q,r)‖≤C) := by
  let K₂ := Metric.closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ D
  let K₃ := Metric.closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ (D ×ˢ D)
  have hK₂ : IsCompact K₂ := (isCompact_closedBall _ _).prod hD
  have hK₃ : IsCompact K₃ := (isCompact_closedBall _ _).prod (hD.prod hD)
  have hA : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) K₂ := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖<ρ := by
      have hh : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
      linarith
    rcases hgood z.1 z.2 0 hs hz.2 hzero with ⟨hB,hU,_,_,_,_,_,hg,_,_⟩
    exact preferredOneBodyExtension_analyticAt z.1 z.2 hU hB hg
  have hK : AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) K₃ := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖<ρ := by
      have hh : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
      linarith
    rcases hgood z.1 z.2.1 z.2.2 hs hz.2.1 hz.2.2 with ⟨hB,hU,hV,_,_,_,_,_,_,hd⟩
    exact preferredKernelExtension_analyticAt z.1 z.2.1 z.2.2 hU hV hB hd
  intro j
  obtain ⟨A,hAb⟩ := hK₂.exists_bound_of_continuousOn (fun z hz =>
    ((hA.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  obtain ⟨B,hBb⟩ := hK₃.exists_bound_of_continuousOn (fun z hz =>
    ((hK.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  refine ⟨max A B+max (-(max A B)) 0+1,?_,?_,?_⟩
  · have := le_max_left (-(max A B)) 0
    linarith
  · intro s q hs hq
    have hz : (s,q)∈K₂ := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq⟩
    exact (hAb (s,q) hz).trans (by
      have := le_max_left A B
      have := le_max_right (-(max A B)) 0
      linarith)
  · intro s q r hs hq hr
    have hz : (s,q,r)∈K₃ := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq,hr⟩
    exact (hBb (s,q,r) hz).trans (by
      have := le_max_right A B
      have := le_max_right (-(max A B)) 0
      linarith)

/-- Uniform diagonal-zero bound on the entire fixed convex regular domain.
It is the actual global patched kernel, not a local near-branch surrogate. -/
theorem preferred_regular_domain_size (d : PreferredBranchData) (ρ c : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D) (hconv : Convex ℝ D) (hzero : (0:ℂ)∈D)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∃ C : ℝ, 0<C ∧ ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D → r∈D →
      ‖preferredOneBodyExtension s q‖≤C ∧ ‖preferredKernelExtension s q r‖≤C*‖q-r‖ := by
  obtain ⟨C₀,hC₀,hA,_⟩ := preferred_regular_domain_all_jets d ρ c D hρ hD hzero hgood 0
  obtain ⟨C₁,hC₁,_,hK⟩ := preferred_regular_domain_all_jets d ρ c D hρ hD hzero hgood 1
  let X := Metric.closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ (D ×ˢ D)
  have hX : Convex ℝ X := (convex_closedBall _ _).prod (hconv.prod hconv)
  have hdiff : ∀ z∈X, DifferentiableAt ℂ
      (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) z := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖<ρ := by
      have hh : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
      linarith
    rcases hgood z.1 z.2.1 z.2.2 hs hz.2.1 hz.2.2 with ⟨hB,hU,hV,_,_,_,_,_,_,hd⟩
    exact (preferredKernelExtension_analyticAt z.1 z.2.1 z.2.2 hU hV hB hd).differentiableAt
  have hbound : ∀ z∈X, ‖fderiv ℂ
      (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) z‖≤C₁ := by
    intro z hz
    have hh := hK z.1 z.2.1 z.2.2
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1) hz.2.1 hz.2.2
    simpa only [norm_iteratedFDeriv_one] using hh
  refine ⟨C₀+C₁,by positivity,?_⟩
  intro s q r hs hq hr
  constructor
  · have hh := hA s q hs hq
    rw [norm_iteratedFDeriv_zero] at hh
    linarith
  · have hx : (s,q,q)∈X := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq,hq⟩
    have hy : (s,q,r)∈X := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq,hr⟩
    have hh := hX.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hx hy
    simp only [preferredKernelExtension_diagonal,sub_zero] at hh
    have he : ‖((s,q,r):ℂ × ℂ × ℂ)-(s,q,q)‖=‖q-r‖ := by
      simp [Prod.norm_def,norm_sub_rev]
    rw [he] at hh
    exact hh.trans (by nlinarith [norm_nonneg (q-r)])

/-- The scalar occupancy coordinate is exactly the coordinate of the
literal coupled N-particle contour; no occupancy is frozen in this identity. -/
theorem preferredBumpCoordinate_actual {N : ℕ} (d : PreferredBranchData)
    (p m : ℝ → ℝ) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    preferredBumpCoordinate d p m ε τ (occupancy p θ/(N:ℝ)) (occupancy m θ/(N:ℝ)) (θ i) =
      preferredSourceCoordinate τ p m (IsingBulk.Branch.radialParameter d.alpha ε) θ i := by
  have hw : preferredBumpAngle m p τ (occupancy p θ/(N:ℝ)) (occupancy m θ/(N:ℝ)) (θ i) =
      deformedAngles τ p m θ i := by
    unfold preferredBumpAngle deformedAngles balancedShift
    push_cast
    ring
  unfold preferredBumpCoordinate
  rw [hw]
  rfl

theorem preferred_occupancy_mean_mem {N : ℕ} (hN : 0<N) (p : ℝ → ℝ)
    (hp : ∀ x, p x ∈ Set.Icc 0 1) (θ : Fin N → ℝ) :
    occupancy p θ/(N:ℝ) ∈ Set.Icc 0 1 := by
  have hN' : 0<(N:ℝ) := by exact_mod_cast hN
  have hlo : 0≤occupancy p θ := Finset.sum_nonneg (fun i _ => (hp (θ i)).1)
  have hhi : occupancy p θ≤(N:ℝ) := by
    calc
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => (hp (θ i)).2)
      _ = _ := by simp
  exact ⟨div_nonneg hlo hN'.le,(div_le_one hN').mpr hhi⟩

theorem preferred_radial_distance (d : PreferredBranchData) (ε : ℝ) :
    ‖IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d‖=|ε| := by
  have he : IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d=
      (ε:ℂ)*Complex.exp ((d.alpha:ℂ)*Complex.I) := by
    simp only [preferredSelectedPoint,IsingBulk.Branch.radialParameter,add_zero,
      Complex.ofReal_one,one_mul,Complex.ofReal_add]
    ring
  rw [he,norm_mul,Complex.norm_exp]
  simp [Complex.mul_re,Real.norm_eq_abs]

/-- The actual whole-right regular coordinate domain can be chosen before
bumps and particle counts. Its upper angular cap is fixed before the bumps,
so a capped smooth plateau fits the exact source partition. -/
theorem preferred_uniform_regular_source_domain (d : PreferredBranchData) :
    ∃ cap ρ c : ℝ, ∃ D : Set ℂ,
      0<cap ∧ cap<d.alpha ∧ 0<ρ ∧ 0<c ∧ IsCompact D ∧ Convex ℝ D ∧ 0∈interior D ∧
      (∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
        PreferredRightRegularPoint c s q r) ∧
      (∀ p m : ℝ → ℝ, Continuous p → Continuous m →
        ∃ r : ℝ, 0<r ∧ ∀ ε τ σ υ θ : ℝ,
          |ε|<r → |τ|<r → σ∈Set.Icc 0 1 → υ∈Set.Icc 0 1 →
          -d.b-r≤θ → θ≤cap → preferredBumpCoordinate d p m ε τ σ υ θ∈interior D) := by
  obtain ⟨V,ρ,c,D,hV,hV',hρ,hc,hD,hconv,hzero,hreal,hgood⟩ :=
    preferred_exists_uniform_regular_domain d
  let cap := min (d.b/2) (min (d.alpha/2) ((V-d.b)/2))
  have hcap : 0<cap := lt_min (half_pos d.b_pos)
    (lt_min (half_pos d.alpha_pos) (half_pos (sub_pos.mpr hV)))
  have hcapb : cap≤d.b := (min_le_left _ _).trans (by linarith [d.b_pos])
  have hcapa : cap<d.alpha := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith [d.alpha_pos])
  have hcapV : cap≤(V-d.b)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hD,hconv,hzero,hgood,?_⟩
  intro p m hp hm
  apply preferred_bump_coordinate_image_fixed d p m hp hm cap hcap.le hcapb D
  intro x hx hx'
  have hv : |x-d.b|≤V := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := hreal (x-d.b) hv
  simpa only [sub_add_cancel] using hh

/-- The full named global inverse obligation is proved for the actual
balanced contour. All constants and the upper cap precede the particle
count; the physical branch identity and every source image are discharged. -/
theorem preferred_global_right_inverse (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ (δ : ℝ), 0<δ → δ<cap → ∀ p m : ℝ → ℝ,
      Continuous p → Continuous m →
      (∀ x, p x∈Set.Icc 0 1) → (∀ x, m x∈Set.Icc 0 1) →
      (∀ x, Real.sin x≤0 → p x=0) → (∀ x, 0≤Real.sin x → m x=0) →
      ∃ τ₀ δB ε₀ : ℝ, 0<τ₀ ∧ 0<δB ∧ 0<ε₀ ∧
        ∀ τ : ℝ, 0≤τ → τ<τ₀ → PreferredGlobalRightInverse d τ p m δ δB ε₀ := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro δ hδ hδcap p m hp hm hpunit hmunit hps hms
  obtain ⟨r,hr,himage⟩ := hsource p m hp hm
  obtain ⟨εs,hεs,hmargin⟩ := preferred_radial_one_sided_margins d δ hδ (hδcap.trans hcapa)
  let δB := min (r/2) ((Real.pi-d.b)/2)
  let ε₀ := min r (min (ρ/2) εs)
  have hδB : 0<δB := lt_min (half_pos hr) (half_pos (sub_pos.mpr d.b_lt))
  have hε₀ : 0<ε₀ := lt_min hr (lt_min (half_pos hρ) hεs)
  have hδBr : δB≤r := (min_le_left _ _).trans (by linarith)
  have hδBπ : δB≤(Real.pi-d.b)/2 := min_le_right _ _
  refine ⟨r,δB,ε₀,hr,hδB,hε₀,?_⟩
  intro τ hτ hτr
  refine ⟨D,ρ,c,hDc,hDv,hzero,hρ,hc,?_,?_⟩
  · intro s q hs hq
    have hh := hgood s q q hs hq hq
    refine ⟨hh.2.1,?_⟩
    change c≤(deriv (deriv (preferredMovingInverse s)) q).re
    rw [← preferredMovingCurvature_eq_deriv s q hh.2.1]
    exact hh.2.2.2.1.le
  · intro N hN ε θ hε hεr hθ i
    dsimp only
    let s := IsingBulk.Branch.radialParameter d.alpha ε
    have hepsr : ε<r := hεr.trans_le (min_le_left _ _)
    have hepss : ε<εs := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hepss
    have hoccP := preferred_occupancy_mean_mem (show 0<N by omega) p hpunit θ
    have hoccM := preferred_occupancy_mean_mem (show 0<N by omega) m hmunit θ
    have himagei := himage ε τ (occupancy p θ/(N:ℝ)) (occupancy m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hepsr)
      (by simpa only [abs_of_nonneg hτ] using hτr) hoccP hoccM
      (by have := (hθ i).1; linarith) ((hθ i).2.trans hδcap.le)
    rw [preferredBumpCoordinate_actual] at himagei
    have hW : 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im := by
      have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) p m θ
        (fun x => (hpunit x).1) (fun x => (hmunit x).1) hps hms i
      simpa only [complexW_homotopyRoot_eq] using hh
    have hwre : (deformedAngles τ p m θ i).re=θ i := by
      simp [deformedAngles,Complex.mul_re]
    refine ⟨himagei,?_,preferredArccos_physical_upper _ hW⟩
    exact preferred_global_one_sided_inverse s (deformedAngles τ p m θ i) δ
      hδ (hδcap.trans (hcapa.trans d.alpha_lt)) hSr hSδ
      (by rw [hwre]; have := (hθ i).1; linarith)
      (by rw [hwre]; exact (hθ i).2) hW

/-- A strictly negative physical phase imaginary part excludes every sine
zero, including the pair-average phase. -/
theorem preferred_sine_ne_zero_of_neg_im (z : ℂ) (hz : z.im<0) : Complex.sin z ≠ 0 := by
  intro hs
  obtain ⟨n,hn⟩ := Complex.sin_eq_zero_iff.mp hs
  have hh := congrArg Complex.im hn
  simp at hh
  linarith

theorem preferredRegularKernel_eq_extension {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (i j : Fin N)
    (hci : Complex.cos ((q i+preferredMovingBranch s)/2) ≠ 0)
    (hcj : Complex.cos ((q j+preferredMovingBranch s)/2) ≠ 0)
    (hφ : Complex.sin ((preferredRegularPhase s (q i)+preferredRegularPhase s (q j))/2) ≠ 0)
    (hD : preferredKernelExtensionDenominator s (q i) (q j) ≠ 0) :
    preferredRegularKernel s q i j=preferredKernelExtension s (q i) (q j) :=
  preferred_half_kernel_extension_identity _ _ _ _ _ (preferredRegular_dispersion s (q i) hci)
    (preferredRegular_dispersion s (q j) hcj) hφ hD

/-- Actual source regular-factor bounds on the complete right contour,
including the negative branch segment and every normalized occupancy.
The cap precedes the bump choice; every remaining constant precedes N. -/
theorem preferred_actual_regular_size (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ (δ : ℝ), 0<δ → δ<cap → ∀ p m : ℝ → ℝ,
      Continuous p → Continuous m →
      (∀ x, p x∈Set.Icc 0 1) → (∀ x, m x∈Set.Icc 0 1) →
      (∀ x, Real.sin x≤0 → p x=0) → (∀ x, 0≤Real.sin x → m x=0) →
      ∃ τ₀ δB ε₀ C : ℝ, 0<τ₀ ∧ 0<δB ∧ 0<ε₀ ∧ 0<C ∧
        ∀ τ : ℝ, 0≤τ → τ<τ₀ → ∀ (N : ℕ), 2≤N → ∀ ε θ,
        0<ε → ε<ε₀ → θ∈preferredRightAngularBox d δ δB N →
        let s := IsingBulk.Branch.radialParameter d.alpha ε
        let q := preferredSourceCoordinate τ p m s θ
        ∀ i, ‖preferredRegularOneBody s (q i)‖≤C ∧
          ∀ j, ‖preferredRegularKernel s q i j‖≤C*‖q i-q j‖ := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  obtain ⟨C,hC,hsize⟩ := preferred_regular_domain_size d ρ c D hρ hDc hDv
    (interior_subset hzero) hgood
  refine ⟨cap,hcap,hcapa,?_⟩
  intro δ hδ hδcap p m hp hm hpunit hmunit hps hms
  obtain ⟨r,hr,himage⟩ := hsource p m hp hm
  obtain ⟨εs,hεs,hmargin⟩ := preferred_radial_one_sided_margins d δ hδ (hδcap.trans hcapa)
  let δB := min (r/2) ((Real.pi-d.b)/2)
  let ε₀ := min r (min (ρ/2) εs)
  have hδB : 0<δB := lt_min (half_pos hr) (half_pos (sub_pos.mpr d.b_lt))
  have hε₀ : 0<ε₀ := lt_min hr (lt_min (half_pos hρ) hεs)
  have hδBr : δB≤r := (min_le_left _ _).trans (by linarith)
  have hδBπ : δB≤(Real.pi-d.b)/2 := min_le_right _ _
  refine ⟨r,δB,ε₀,C,hr,hδB,hε₀,hC,?_⟩
  intro τ hτ hτr N hN ε θ hε hεr hθ
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ p m s θ
  have hepsr : ε<r := hεr.trans_le (min_le_left _ _)
  have hepss : ε<εs := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hepsρ : ε<ρ/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hepsρ.le
  have hs' : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hepss
  have hoccP := preferred_occupancy_mean_mem (show 0<N by omega) p hpunit θ
  have hoccM := preferred_occupancy_mean_mem (show 0<N by omega) m hmunit θ
  have hq (i : Fin N) : q i∈D := by
    apply interior_subset
    have hh := himage ε τ (occupancy p θ/(N:ℝ)) (occupancy m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hepsr)
      (by simpa only [abs_of_nonneg hτ] using hτr) hoccP hoccM
      (by have := (hθ i).1; linarith) ((hθ i).2.trans hδcap.le)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  have hW (i : Fin N) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im := by
    have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) p m θ
      (fun x => (hpunit x).1) (fun x => (hmunit x).1) hps hms i
    simpa only [complexW_homotopyRoot_eq] using hh
  have hphase (i : Fin N) : (preferredRegularPhase s (q i)).im<0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    have hU := preferred_global_one_sided_inverse s (deformedAngles τ p m θ i) δ
      hδ (hδcap.trans (hcapa.trans d.alpha_lt)) hSr hSδ
      (by rw [hwre]; have := (hθ i).1; linarith)
      (by rw [hwre]; exact (hθ i).2) (hW i)
    change preferredMovingInverse s (q i)=deformedAngles τ p m θ i at hU
    have heq : preferredRegularPhase s (q i)=preferredSourcePhase τ p m s θ i := by
      unfold preferredRegularPhase
      rw [hU]
      dsimp [q,preferredSourceCoordinate]
      ring
    rw [heq]
    exact (IsingBulk.Branch.lowerArccos_sheet_of_upper (hW i)).2.2.2
  intro i
  rcases hgood s (q i) (q i) hs' (hq i) (hq i) with
    ⟨hB,hUi,_,_,_,hci,_,_,_,_⟩
  have hUid : DifferentiableAt ℂ (preferredMovingInverse s) (q i) :=
    (AnalyticAt.comp (f := fun v : ℂ => (s,v))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hUi
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  constructor
  · rw [preferredRegularOneBody_eq_extension s (q i) hci hUid
      (preferred_sine_ne_zero_of_neg_im _ (hphase i))]
    exact (hsize s (q i) (q i) hs (hq i) (hq i)).1
  · intro j
    rcases hgood s (q i) (q j) hs' (hq i) (hq j) with
      ⟨_,_,_,_,_,_,hcj,_,_,hden⟩
    have hφ : Complex.sin ((preferredRegularPhase s (q i)+preferredRegularPhase s (q j))/2) ≠ 0 := by
      apply preferred_sine_ne_zero_of_neg_im
      have he : ((preferredRegularPhase s (q i)+preferredRegularPhase s (q j))/2).im=
          ((preferredRegularPhase s (q i)).im+(preferredRegularPhase s (q j)).im)/2 := by
        simp
      rw [he]
      linarith [hphase i,hphase j]
    rw [preferredRegularKernel_eq_extension s q i j hci hcj hφ hden]
    exact (hsize s (q i) (q j) hs (hq i) (hq j)).2

/-- All true parameter jets of Uq vanish on the moving center on one fixed
parameter neighborhood. The radius is selected before the derivative order. -/
theorem preferredParameterQJet_center_all (d : PreferredBranchData) :
    ∃ R : ℝ, 0<R ∧ ∀ s : ℂ, ‖s-preferredSelectedPoint d‖<R →
      ∀ n : ℕ, preferredParameterQJet n (s,0)=0 := by
  have hU := preferredMovingInverse_analyticAt_reference d
  have ht : Filter.Tendsto (fun s : ℂ => (s,(0:ℂ)))
      (𝓝 (preferredSelectedPoint d)) (𝓝 (preferredSelectedPoint d,0)) :=
    (show Continuous (fun s : ℂ => (s,(0:ℂ))) by fun_prop).tendsto _
  have he := (ht.eventually hU.eventually_analyticAt).and (preferredMovingInverse_center_germ d)
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨R,hR,?_⟩
  intro s hs n
  have hs' : dist s (preferredSelectedPoint d)<R := by simpa only [dist_eq_norm] using hs
  have hz : (fun t : ℂ => deriv (preferredMovingInverse t) 0) =ᶠ[𝓝 s] (fun _ => (0:ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hs'] with t ht
    exact (hball ht).2.2
  rw [preferredParameterQJet_eq_iteratedDeriv n s 0 (hball hs').1]
  simpa using hz.iteratedDeriv_eq n

/-- Source (7.16) on the whole fixed convex domain, for genuine physical
parameter jets. The parameter radius is fixed before every order n. -/
theorem preferred_global_parameter_q_bound (d : PreferredBranchData) (ρ : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hDc : IsCompact D) (hDv : Convex ℝ D) (hzero : (0:ℂ)∈D)
    (hU : ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    ∃ R : ℝ, 0<R ∧ R≤ρ/2 ∧ ∀ n : ℕ, ∃ C : ℝ, 0<C ∧
      ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖≤R → q∈D →
        ‖preferredParameterQJet n (s,q)‖≤C*‖q‖ := by
  obtain ⟨R₀,hR₀,hcenter⟩ := preferredParameterQJet_center_all d
  let R := min (ρ/2) (R₀/2)
  have hR : 0<R := lt_min (half_pos hρ) (half_pos hR₀)
  have hRρ : R≤ρ/2 := min_le_left _ _
  have hRR₀ : R<R₀ := (min_le_right _ _).trans_lt (by linarith)
  let X := Metric.closedBall (preferredSelectedPoint d) R ×ˢ D
  have hXc : IsCompact X := (isCompact_closedBall _ _).prod hDc
  have hXv : Convex ℝ X := (convex_closedBall _ _).prod hDv
  refine ⟨R,hR,hRρ,?_⟩
  intro n
  have hQ : AnalyticOnNhd ℂ (preferredParameterQJet n) X := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤R := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact preferredParameterQJet_analyticAt n z (hU z.1 z.2 (by linarith) hz.2)
  obtain ⟨M,hMb⟩ := hXc.exists_bound_of_continuousOn
    (fun z hz => (hQ z hz).fderiv.continuousAt.continuousWithinAt)
  let C := max M 0+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s q hs hq
  have hx : (s,(0:ℂ))∈X := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hzero⟩
  have hy : (s,q)∈X := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq⟩
  have hbound : ∀ z∈X, ‖fderiv ℂ (preferredParameterQJet n) z‖≤C := by
    intro z hz
    exact (hMb z hz).trans (by dsimp [C]; have := le_max_left M 0; linarith)
  have hh := hXv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hQ z hz).differentiableAt) hbound hx hy
  rw [hcenter s (hs.trans_lt hRR₀) n,sub_zero] at hh
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,sub_zero,norm_zero,
    max_eq_right (norm_nonneg q)] using hh

/-- Source (7.17) on the same fixed convex right domain, with actual
parameter derivatives of the literal pair inverse difference. No epsilon
loss or parameter-dependent collision cost is introduced. -/
theorem preferred_global_parameter_pair_bound (d : PreferredBranchData) (ρ : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hDc : IsCompact D) (hDv : Convex ℝ D) (hzero : (0:ℂ)∈D)
    (hU : ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    ∃ R : ℝ, 0<R ∧ R≤ρ/2 ∧ ∀ n : ℕ, ∃ C : ℝ, 0<C ∧
      ∀ s q₁ q₂ : ℂ, ‖s-preferredSelectedPoint d‖≤R → q₁∈D → q₂∈D →
        ‖iteratedDeriv n (fun t => preferredMovingInverse t q₁-preferredMovingInverse t q₂) s‖≤
          C*max ‖q₁‖ ‖q₂‖*‖q₁-q₂‖ := by
  obtain ⟨R,hR,hRρ,hbound⟩ := preferred_global_parameter_q_bound d ρ D hρ hDc hDv hzero hU
  refine ⟨R,hR,hRρ,?_⟩
  intro n
  obtain ⟨C,hC,hqbound⟩ := hbound n
  refine ⟨C,hC,?_⟩
  intro s q₁ q₂ hs hq₁ hq₂
  have hsρ : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  let B := max ‖q₁‖ ‖q₂‖
  let E := D ∩ Metric.closedBall (0:ℂ) B
  have hEv : Convex ℝ E := hDv.inter (convex_closedBall _ _)
  have hder (q : ℂ) (hq : q∈E) :
      HasDerivWithinAt (fun v => preferredParameterUJet n (s,v))
        (preferredParameterQJet n (s,q)) E q :=
    (preferredParameterUJet_hasDerivAt_q n s q (hU s q hsρ hq.1)).hasDerivWithinAt
  have hderbound (q : ℂ) (hq : q∈E) : ‖preferredParameterQJet n (s,q)‖≤C*B := by
    have hqB : ‖q‖≤B := by simpa only [Metric.mem_closedBall,dist_zero_right] using hq.2
    exact (hqbound s q hs hq.1).trans (mul_le_mul_of_nonneg_left hqB hC.le)
  have h₁ : q₁∈E := ⟨hq₁,by simpa only [Metric.mem_closedBall,dist_zero_right] using le_max_left ‖q₁‖ ‖q₂‖⟩
  have h₂ : q₂∈E := ⟨hq₂,by simpa only [Metric.mem_closedBall,dist_zero_right] using le_max_right ‖q₁‖ ‖q₂‖⟩
  have hmv := hEv.norm_image_sub_le_of_norm_hasDerivWithin_le hder hderbound h₂ h₁
  have ha₁ : AnalyticAt ℂ (fun t => preferredMovingInverse t q₁) s :=
    AnalyticAt.comp (f := fun t : ℂ => (t,q₁))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (hU s q₁ hsρ hq₁)
      (analyticAt_id.prod analyticAt_const)
  have ha₂ : AnalyticAt ℂ (fun t => preferredMovingInverse t q₂) s :=
    AnalyticAt.comp (f := fun t : ℂ => (t,q₂))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (hU s q₂ hsρ hq₂)
      (analyticAt_id.prod analyticAt_const)
  rw [iteratedDeriv_fun_sub (ha₁.contDiffAt (n := n)) (ha₂.contDiffAt (n := n)),
    ← preferredParameterUJet_eq_iteratedDeriv n s q₁ (hU s q₁ hsρ hq₁),
    ← preferredParameterUJet_eq_iteratedDeriv n s q₂ (hU s q₂ hsρ hq₂)]
  exact hmv

/-- Uniform source interior margin obtained by an inner compact thickening.
No joint boundary continuity is assumed at negative u: the proved physical
source image is placed in the inner thickening before the margin is used. -/
theorem preferred_bump_coordinate_image_margin (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) (δR : ℝ) (hδR : 0≤δR) (hδRb : δR≤d.b)
    (D : Set ℂ) (hD : ∀ x : ℝ, 0≤x → x≤2*d.b+δR → (x:ℂ)∈interior D) :
    ∃ κ r : ℝ, 0<κ ∧ 0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → σ∈Set.Icc 0 1 → υ∈Set.Icc 0 1 →
      -d.b-r≤θ → θ≤δR →
      Metric.closedBall (preferredBumpCoordinate d p m ε τ σ υ θ) κ ⊆ D := by
  let K : Set ℂ := Complex.ofReal '' Set.Icc 0 (2*d.b+δR)
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKD : K⊆interior D := by
    rintro x ⟨y,hy,rfl⟩
    exact hD y hy.1 hy.2
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_thickening_subset_open isOpen_interior hKD
  let κ := δ/4
  have hκ : 0<κ := by dsimp [κ]; positivity
  let E := Metric.cthickening κ K
  have hE : ∀ x : ℝ, 0≤x → x≤2*d.b+δR → (x:ℂ)∈interior E := by
    intro x hx hx'
    exact (Metric.thickening_subset_interior_cthickening κ K)
      (Metric.self_subset_thickening hκ K ⟨x,⟨hx,hx'⟩,rfl⟩)
  obtain ⟨r,hr,himage⟩ := preferred_bump_coordinate_image_fixed d p m hp hm δR hδR hδRb E hE
  refine ⟨κ,r,hκ,hr,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθL hθR z hz
  have hq : preferredBumpCoordinate d p m ε τ σ υ θ∈E :=
    interior_subset (himage ε τ σ υ θ hε hτ hσ hυ hθL hθR)
  have hq' : preferredBumpCoordinate d p m ε τ σ υ θ∈Metric.thickening (δ/2) K :=
    Metric.cthickening_subset_thickening' (half_pos hδ) (by dsimp [κ]; linarith) K hq
  obtain ⟨a,ha,hqa⟩ := Metric.mem_thickening_iff.mp hq'
  have hza : dist z a<δ := by
    have hzq : dist z (preferredBumpCoordinate d p m ε τ σ υ θ)≤κ := hz
    have hh := dist_triangle z (preferredBumpCoordinate d p m ε τ σ υ θ) a
    dsimp [κ] at hzq
    linarith
  exact interior_subset (hthick (Metric.mem_thickening_iff.mpr ⟨a,ha,hza⟩))

/-- Fixed analytic domain together with an N-independent complex q margin
for every actual scalar occupancy coordinate. This is the source input for
anisotropic Cauchy estimates of the collective field. -/
theorem preferred_uniform_regular_source_domain_with_margin (d : PreferredBranchData) :
    ∃ cap ρ c : ℝ, ∃ D : Set ℂ,
      0<cap ∧ cap<d.alpha ∧ 0<ρ ∧ 0<c ∧ IsCompact D ∧ Convex ℝ D ∧ 0∈interior D ∧
      (∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
        PreferredRightRegularPoint c s q r) ∧
      (∀ p m : ℝ → ℝ, Continuous p → Continuous m →
        ∃ κ r : ℝ, 0<κ ∧ 0<r ∧ ∀ ε τ σ υ θ : ℝ,
          |ε|<r → |τ|<r → σ∈Set.Icc 0 1 → υ∈Set.Icc 0 1 →
          -d.b-r≤θ → θ≤cap →
          Metric.closedBall (preferredBumpCoordinate d p m ε τ σ υ θ) κ⊆D) := by
  obtain ⟨V,ρ,c,D,hV,hV',hρ,hc,hD,hconv,hzero,hreal,hgood⟩ :=
    preferred_exists_uniform_regular_domain d
  let cap := min (d.b/2) (min (d.alpha/2) ((V-d.b)/2))
  have hcap : 0<cap := lt_min (half_pos d.b_pos)
    (lt_min (half_pos d.alpha_pos) (half_pos (sub_pos.mpr hV)))
  have hcapb : cap≤d.b := (min_le_left _ _).trans (by linarith [d.b_pos])
  have hcapa : cap<d.alpha := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith [d.alpha_pos])
  have hcapV : cap≤(V-d.b)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hD,hconv,hzero,hgood,?_⟩
  intro p m hp hm
  apply preferred_bump_coordinate_image_margin d p m hp hm cap hcap.le hcapb D
  intro x hx hx'
  have hv : |x-d.b|≤V := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := hreal (x-d.b) hv
  simpa only [sub_add_cancel] using hh

end
end IsingBulk.Preferred22
