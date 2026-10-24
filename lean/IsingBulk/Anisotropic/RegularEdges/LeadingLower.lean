import IsingBulk.Anisotropic.RegularEdges.LeadingAmplitude

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter Metric
open scoped Topology

theorem edgeShapeDenominator_continuousAt_zero {n : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) :
    ContinuousAt (fun p : ℝ×ShapeSpace n => edgeShapeDenominator b B p.1 p.2) 0 := by
  have hG : Continuous (fun p : ℝ×ShapeSpace n =>
      (Complex.I*(p.1:ℂ)^2,fun i : Fin (n+1) => (p.2.1 i:ℂ))) := by fun_prop
  have h := (edgeComplexDenominator_analyticAt (N := n+1) hb hB).continuousAt
  exact h.comp_of_eq hG.continuousAt (by ext <;> simp)

theorem edgeShapeDenominator_tendsto_zero {n : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (x : ShapeSpace n) :
    Tendsto (fun t : ℝ => edgeShapeDenominator b B t (t • x)) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => (t,t • x)) (𝓝[>] 0) (𝓝 ((0,0):ℝ×ShapeSpace n)) := by
    have hct : Continuous (fun t : ℝ => (t,t • x)) := by fun_prop
    simpa using! (hct.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hh := (edgeShapeDenominator_continuousAt_zero (n := n) hb hB).tendsto.comp hp
  have hz : edgeShapeDenominator (n := n) b B 0 0=0 := by
    simp [edgeShapeDenominator,edgeComplexDenominator,hres]
  change Tendsto (fun t : ℝ => edgeShapeDenominator b B t (t • x)) (𝓝[>] 0)
    (𝓝 (edgeShapeDenominator b B 0 0)) at hh
  rwa [hz] at hh

/-- Lower derivative terms vanish after the leading normalization, including the logarithmic odd case. -/
theorem exists_edgeActualLocal_lower_limit {n k a j : ℕ} (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} {B S : ℂ→ℂ} (hb : |b|<1) (hB : AnalyticAt ℂ B 0)
    (hBi : 0<(B 0).im) (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃ R : ℝ,0<R ∧ R≤Real.pi ∧
      Tendsto (fun t : ℝ => (t^a) • edgeActualLocalDerivativeIntegral (n := n) b B S j R t)
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R,M,hR,hRπ,hM,hlocal⟩ := edgeShape_local_bounds (n := n) hb hB hBi hS hS0 j
  obtain ⟨c,δ,hc,hδ,hgap⟩ := edgeShapeDenominator_gap (n := n) (b := b) hBi hB.continuousAt
  obtain ⟨r,hr,heq⟩ := edgeActualLocalDerivativeIntegral_eventually_eq (n := n) hb hB hBi hS hS0
  have hD0 : edgeShapeDenominator (n := n) b B 0 0=0 := by
    simp [edgeShapeDenominator,edgeComplexDenominator,hres]
  have hsmall : ∀ᶠ p : ℝ×ShapeSpace n in 𝓝 0,‖edgeShapeDenominator b B p.1 p.2‖<1 :=
    (edgeShapeDenominator_continuousAt_zero (n := n) hb hB).norm.eventually_lt continuousAt_const
      (by change ‖edgeShapeDenominator b B 0 0‖<1; rw [hD0,norm_zero]; norm_num)
  obtain ⟨rD,hrD,hsmallball⟩ := Metric.eventually_nhds_iff.mp hsmall
  let L := min R (min r rD)
  have hL : 0<L := lt_min hR (lt_min hr hrD)
  have hLR : L≤R := min_le_left _ _
  have hLr : L≤r := (min_le_right _ _).trans (min_le_left _ _)
  have hLD : L≤rD := (min_le_right _ _).trans (min_le_right _ _)
  have hδL : 0<min L δ := lt_min hL hδ
  have htR (t : ℝ) (ht : t∈Ioo 0 (min L δ)) : |t|<R := by
    rw [abs_of_pos ht.1]
    exact ht.2.trans_le ((min_le_left _ _).trans hLR)
  have hDsmall (t : ℝ) (ht : t∈Ioo 0 (min L δ)) (x : ShapeSpace n) (hx : x∈ball 0 L) :
      ‖edgeShapeDenominator b B t x‖≤1 := by
    apply (hsmallball (y := (t,x)) ?_).le
    rw [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (max_lt (ht.2.trans_le (min_le_left _ _)) (by simpa using hx)).trans_le hLD
  have hangle (x : ShapeSpace n) (hx : x∈ball 0 L) (i : Fin (n+1)) :
      x.1 i∈Icc (-Real.pi) Real.pi := by
    have hnorm : ‖x‖<L := by simpa using hx
    have hh := PiLp.norm_apply_le x.1 i
    rw [Real.norm_eq_abs] at hh
    have hh' : |x.1 i|<Real.pi := hh.trans_lt (hnorm.trans_le (hLR.trans hRπ))
    exact ⟨(abs_lt.mp hh').1.le,(abs_lt.mp hh').2.le⟩
  let A : ℝ→ShapeSpace n→ℂ := fun t x => edgeShapeAmplitude b B S j t x*
    edgeShapeDenominator b B t x^(k-j)
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  obtain ⟨hchi,hchi0,hchib,hchis⟩ := edgeShapeCutoff_properties (n := n) hL
  have hlim := edge_shape_cutoff_limit hbalance hmajorant A (edgeShapeDenominator b B)
    (edgeShapeCutoff L) 0 hL (div_pos (by positivity : 0<(n+1:ℝ)) hs)
    (edge_quadratic_re_pos hBi (mul_pos (by norm_num : (0:ℝ)<2) hs)) hM hc hδL
    hchi hchi0 hchib hchis
    (fun t ht => ((hlocal t (htR t ht)).1.mul ((hlocal t (htR t ht)).2.1.pow _)).mono (ball_subset_ball hLR))
    (fun t ht => (hlocal t (htR t ht)).2.1.mono (ball_subset_ball hLR))
    (fun t ht x hx => show ‖A t x‖≤M from by
      dsimp only [A]
      rw [norm_mul,norm_pow]
      calc
        _ ≤ M*1 := mul_le_mul ((hlocal t (htR t ht)).2.2 x (ball_subset_ball hLR hx))
          (pow_le_one₀ (norm_nonneg _) (hDsmall t ht x hx)) (by positivity) hM
        _ = M := mul_one _)
    (fun t ht x hx => hgap t ht.1 (ht.2.trans_le (min_le_right _ _)) x (hangle x hx))
    (fun x => show Tendsto (fun t => A t (t • x)) (𝓝[>] 0) (𝓝 0) from by
      have hh := (edgeShapeAmplitude_scaled_limit hb hB hBi hS hS0 j x).mul
        ((edgeShapeDenominator_tendsto_zero hb hB hres x).pow (k-j))
      simpa only [A,zero_pow (Nat.sub_pos_of_lt hj).ne',mul_zero] using! hh)
    (edgeShapeDenominator_scaled_limit hb hB.continuousAt hres)
  simp only [zero_mul] at hlim
  refine ⟨L,hL,hLR.trans hRπ,hlim.congr' ?_⟩
  filter_upwards [heq L hL hLr j,self_mem_nhdsWithin,
    (eventually_lt_nhds hδL).filter_mono nhdsWithin_le_nhds] with t he ht htδ
  rw [he]
  congr 1
  unfold edgeLocalJetIntegral
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : edgeShapeCutoff L x=0
  · simp [hx]
  · have hmem : x∈ball 0 L := by simpa using hchis x hx
    have hn : edgeShapeDenominator b B t x≠0 := by
      intro he0
      have hg := hgap t ht (htδ.trans_le (min_le_right _ _)) x (hangle x hmem)
      rw [he0,norm_zero] at hg
      have htpos : 0<t := ht
      have hp : 0<c*(t^2+‖x‖^2) := by positivity
      linarith
    have hepow : edgeShapeDenominator b B t x^(k+1)=
        edgeShapeDenominator b B t x^(j+1)*edgeShapeDenominator b B t x^(k-j) := by
      rw [←pow_add]
      congr 1
      omega
    rw [hepow]
    dsimp [A]
    field_simp

end
end IsingBulk.Anisotropic.RegularEdges
