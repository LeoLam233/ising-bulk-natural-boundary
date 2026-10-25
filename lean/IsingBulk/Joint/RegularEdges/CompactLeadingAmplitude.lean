import IsingBulk.Joint.RegularEdges.PositiveFullSum

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology

/-- The actual coefficient of the selected singular derivative, evaluated at
independent complex chart data. No model amplitude is substituted for it. -/
def independentLeadingAmplitude (n k : ℕ) (b : ℝ) (v : ℂ × ℂ) : ℂ :=
  edgeCoefficientLeading n k b (fun _ => v.1) (fun _ => v.2)

theorem edgeCoefficientLeading_eq_period (n k : ℕ) (b : ℝ) (B S : ℂ → ℂ) :
    edgeCoefficientLeading n k b B S = edgeCoefficientNormalization n *
      edgeAnalyticJet b B S k (0,(0:Fin (n+1)→ℂ)) *
      shapePeriod n k ((n+1)/Real.sqrt (1-b^2))
        (-Complex.I*B 0/((2*Real.sqrt (1-b^2):ℝ):ℂ)) := by
  unfold edgeCoefficientLeading edgeFullLeadingCoefficient edgeLeadingCoefficient
  rw [shapePeriod_eq_intrinsic]
  simp only [Complex.real_smul]
  ring

/-- All curve dependence in the leading coefficient is its actual central
chart data; nonconstant B is not replaced inside the original integral. -/
theorem edgeCoefficientLeading_eq_center (n k : ℕ) {b : ℝ} (hb : |b|<1)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) (B S : ℂ → ℂ) :
    edgeCoefficientLeading n k b B S = independentLeadingAmplitude n k b (B 0,S 0) := by
  simp only [independentLeadingAmplitude,edgeCoefficientLeading_eq_period,
    edgeAnalyticJet_collision (Nat.succ_pos _) hb _ _ hres k,
    edgeRegularAmplitude_collision]

theorem even_shapePeriod_continuousOn {n k : ℕ} (hn : 1≤n)
    (hd : n-1+(n+1)*n=2*k) {Q : ℝ} (hQ : 0<Q) :
    ContinuousOn (shapePeriod n k Q) {c : ℂ | 0<c.re} := by
  have h := (shapeRadialIntegral_analyticOnNhd k hQ).continuousOn
  apply (h.const_smul (shapeAngularConstant n)).congr
  intro c _
  exact shapePeriod_eq_radial hn hd Q c

theorem odd_shapePeriod_continuousOn {n m : ℕ} (hn : 1≤n)
    (hd : n-1+(n+1)*n=2*m+1) {Q : ℝ} (hQ : 0<Q) :
    ContinuousOn (shapePeriod n (m+1) Q) {c : ℂ | 0<c.re} := by
  have hq : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hc : ContinuousOn (fun c : ℂ => 1/(2*((m+1:ℕ):ℂ)*(Q:ℂ)*c^(m+1)))
      {c : ℂ | 0<c.re} := by
    apply continuousOn_const.div
      ((continuousOn_const.mul continuousOn_const).mul continuousOn_const |>.mul (continuousOn_id.pow _))
    intro c hc
    have hnz : c≠0 := by intro he; simp [he] at hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (by omega))) hq) (pow_ne_zero _ hnz)
  apply (hc.const_smul (shapeAngularConstant n)).congr
  intro c hc
  rw [shapePeriod_odd_eq_radial hn hd,oddRadialKernel_integral m hQ hc]
  rfl

theorem independentLeadingAmplitude_continuousAt {n k : ℕ} {b : ℝ}
    (hb : |b|<1) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hperiod : ContinuousOn (shapePeriod n k ((n+1)/Real.sqrt (1-b^2)))
      {c : ℂ | 0<c.re})
    {v : ℂ × ℂ} (hB : 0<v.1.im) (hS : v.2≠0) :
    ContinuousAt (independentLeadingAmplitude n k b) v := by
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hj : ContinuousAt (fun w : ℂ × ℂ =>
      edgeAnalyticJet b (fun _ => w.1) (fun _ => w.2) k (0,(0:Fin (n+1)→ℂ))) v := by
    simp_rw [edgeAnalyticJet_collision (Nat.succ_pos _) hb _ _ hres k,
      edgeRegularAmplitude_collision]
    have hi := continuousAt_snd.inv₀ hS
    fun_prop
  have hq : 0<(-Complex.I*v.1/((2*Real.sqrt (1-b^2):ℝ):ℂ)).re :=
    edge_quadratic_re_pos hB (by positivity)
  have hp : ContinuousAt (fun w : ℂ × ℂ =>
      shapePeriod n k ((n+1)/Real.sqrt (1-b^2))
        (-Complex.I*w.1/((2*Real.sqrt (1-b^2):ℝ):ℂ))) v :=
    (hperiod.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq)).comp
        (f := fun w : ℂ × ℂ => -Complex.I*w.1/((2*Real.sqrt (1-b^2):ℝ):ℂ)) (by fun_prop)
  have hh := (hj.const_mul (edgeCoefficientNormalization n)).mul hp
  convert hh using 1
  funext w
  exact edgeCoefficientLeading_eq_period n k b (fun _ => w.1) (fun _ => w.2)

/-- Ordinary compactness turns actual continuous nonzero amplitudes into a
single positive lower bound; an empty family is handled without an existence
assumption or a choice of a fake family member. -/
theorem compact_nonzero_norm_lower_bound {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {f : E → ℂ}
    (hf : ContinuousOn f K) (hne : ∀ x∈K, f x≠0) :
    ∃ c : ℝ, 0<c ∧ ∀ x∈K, c≤‖f x‖ := by
  by_cases hneK : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hneK hf.norm
    exact ⟨‖f x‖,norm_pos_iff.mpr (hne x hx),fun y hy => hmin hy⟩
  · refine ⟨1,by norm_num,?_⟩
    intro x hx
    exact False.elim (hneK ⟨x,hx⟩)

theorem even_compact_leading_amplitude_lower_bound {n k : ℕ} (hn : 1≤n)
    (hd : n-1+(n+1)*n=2*k) {b : ℝ} (hb : |b|<1)
    (hres : continuedRoot (b:ℂ)^(n+1)=1)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ c : ℝ, 0<c ∧ ∀ v∈K, c≤‖independentLeadingAmplitude n k b v‖ := by
  have hb' := abs_lt.mp hb
  have hQ : 0<(n+1)/Real.sqrt (1-b^2) :=
    div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  apply compact_nonzero_norm_lower_bound hK
  · intro v hv
    exact (independentLeadingAmplitude_continuousAt hb hres
      (even_shapePeriod_continuousOn hn hd hQ) (hB v hv) (hS v hv)).continuousWithinAt
  · intro v hv
    exact mul_ne_zero (edgeCoefficientNormalization_ne_zero n)
      (even_edge_full_leading_amplitude hn hd hb analyticAt_const (hB v hv)
        analyticAt_const (hS v hv) hres).1

theorem odd_compact_leading_amplitude_lower_bound {n m : ℕ} (hn : 1≤n)
    (hd : n-1+(n+1)*n=2*m+1) {b : ℝ} (hb : |b|<1)
    (hres : continuedRoot (b:ℂ)^(n+1)=1)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ c : ℝ, 0<c ∧ ∀ v∈K, c≤‖independentLeadingAmplitude n (m+1) b v‖ := by
  have hb' := abs_lt.mp hb
  have hQ : 0<(n+1)/Real.sqrt (1-b^2) :=
    div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  apply compact_nonzero_norm_lower_bound hK
  · intro v hv
    exact (independentLeadingAmplitude_continuousAt hb hres
      (odd_shapePeriod_continuousOn hn hd hQ) (hB v hv) (hS v hv)).continuousWithinAt
  · intro v hv
    exact mul_ne_zero (edgeCoefficientNormalization_ne_zero n)
      (odd_edge_full_leading_amplitude hn hd hb analyticAt_const (hB v hv)
        analyticAt_const (hS v hv) hres).1

theorem even_family_leading_amplitude_lower_bound
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {B S : E → ℂ → ℂ} (hBc : ContinuousOn (fun e => B e 0) K)
    (hSc : ContinuousOn (fun e => S e 0) K)
    (hB : ∀ e∈K, 0<(B e 0).im) (hS : ∀ e∈K, S e 0≠0)
    {n k : ℕ} (hn : 1≤n) (hd : n-1+(n+1)*n=2*k)
    {b : ℝ} (hb : |b|<1) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃ c : ℝ, 0<c ∧ ∀ e∈K, c≤‖edgeCoefficientLeading n k b (B e) (S e)‖ := by
  let f : E → ℂ × ℂ := fun e => (B e 0,S e 0)
  have hc : IsCompact (f '' K) := hK.image_of_continuousOn (hBc.prodMk hSc)
  obtain ⟨c,hcpos,hbound⟩ := even_compact_leading_amplitude_lower_bound hn hd hb hres hc
    (by rintro v ⟨e,he,rfl⟩; exact hB e he)
    (by rintro v ⟨e,he,rfl⟩; exact hS e he)
  refine ⟨c,hcpos,?_⟩
  intro e he
  rw [edgeCoefficientLeading_eq_center n k hb hres]
  exact hbound (f e) (mem_image_of_mem f he)

theorem odd_family_leading_amplitude_lower_bound
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {B S : E → ℂ → ℂ} (hBc : ContinuousOn (fun e => B e 0) K)
    (hSc : ContinuousOn (fun e => S e 0) K)
    (hB : ∀ e∈K, 0<(B e 0).im) (hS : ∀ e∈K, S e 0≠0)
    {n m : ℕ} (hn : 1≤n) (hd : n-1+(n+1)*n=2*m+1)
    {b : ℝ} (hb : |b|<1) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃ c : ℝ, 0<c ∧ ∀ e∈K, c≤‖edgeCoefficientLeading n (m+1) b (B e) (S e)‖ := by
  let f : E → ℂ × ℂ := fun e => (B e 0,S e 0)
  have hc : IsCompact (f '' K) := hK.image_of_continuousOn (hBc.prodMk hSc)
  obtain ⟨c,hcpos,hbound⟩ := odd_compact_leading_amplitude_lower_bound hn hd hb hres hc
    (by rintro v ⟨e,he,rfl⟩; exact hB e he)
    (by rintro v ⟨e,he,rfl⟩; exact hS e he)
  refine ⟨c,hcpos,?_⟩
  intro e he
  rw [edgeCoefficientLeading_eq_center n (m+1) hb hres]
  exact hbound (f e) (mem_image_of_mem f he)

/-- Uniform nonvanishing survives actual nonzero physical and nonramified
coordinate factors; the full scaled-limit identity is proved separately. -/
theorem compact_weighted_leading_lower_bound
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {a d f : E → ℂ} (ha : ContinuousOn a K) (hd : ContinuousOn d K)
    (hf : ContinuousOn f K) (hna : ∀ e∈K, a e≠0)
    (hnd : ∀ e∈K, d e≠0) (hnf : ∀ e∈K, f e≠0) (j : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ e∈K, c≤‖a e*(d e)^j*f e‖ :=
  compact_nonzero_norm_lower_bound hK ((ha.mul (hd.pow j)).mul hf)
    (fun e he => mul_ne_zero (mul_ne_zero (hna e he) (pow_ne_zero j (hnd e he))) (hnf e he))

end
end IsingBulk.Joint.RegularEdges
