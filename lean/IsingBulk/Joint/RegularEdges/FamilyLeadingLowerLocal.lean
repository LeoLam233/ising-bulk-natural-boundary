import IsingBulk.Joint.RegularEdges.FamilyLeadingLowerSupport

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every lower derivative of the first resonant coefficient vanishes after
the leading normalization, jointly in the time and complex parameter. -/
theorem compact_family_lowerLocalJet_joint_limit {n k a j : ℕ} (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃R : ℝ,0<R ∧ R≤Real.pi ∧ ∀R' : ℝ,0<R' → R'≤R → ∀eta₀∈Q,
      Tendsto (fun p : ℝ × E => (p.1^a) • edgeLocalJetIntegral (n:=n)
        b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) j R' p.1)
        (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) := by
  obtain ⟨R,M,hR,hRπ,hM,hlocal⟩ := compact_family_shape_local_bounds (n:=n) B S hb hQ hB hBi hS hS0 j
  obtain ⟨c,δ,hc,hδ,hgap⟩ := compact_family_shapeDenominator_gap (n:=n) B hb hQ hB hBi
  obtain ⟨r,hr,hdata⟩ := compact_family_upper_data B S hQ hB hBi hS hS0
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hP : 0<(n+1:ℝ)/Real.sqrt (1-b^2) := div_pos (by positivity) hs
  refine ⟨R,hR,hRπ,?_⟩
  intro R' hR' hR'R eta₀ heta₀
  let l := 𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)
  have hτ : Tendsto (fun p : ℝ × E => p.1) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1
  have heta : Tendsto (fun p : ℝ × E => p.2) l (𝓝 eta₀) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htime : ∀ᶠ p : ℝ × E in l, 0<p.1 ∧ p.1<min R (min δ (Real.sqrt r)) ∧ p.2∈Q := by
    filter_upwards [self_mem_nhdsWithin,
      (hτ.mono_right nhdsWithin_le_nhds).eventually
        (eventually_lt_nhds (lt_min hR (lt_min hδ (Real.sqrt_pos.mpr hr))))] with p hp ht
    exact ⟨hp.1,ht,hp.2⟩
  have hangle (x : ShapeSpace n) (hx : x∈ball 0 R') (i : Fin (n+1)) :
      x.1 i∈Icc (-Real.pi) Real.pi := by
    have hnorm : ‖x‖<R := (show ‖x‖<R' by simpa using hx).trans_le hR'R
    have hangle := PiLp.norm_apply_le x.1 i
    rw [Real.norm_eq_abs] at hangle
    have hlt : |x.1 i|<Real.pi := hangle.trans_lt (hnorm.trans_le hRπ)
    exact ⟨(abs_lt.mp hlt).1.le,(abs_lt.mp hlt).2.le⟩
  let AA : (ℝ × E) → ShapeSpace n → ℂ := fun p x =>
    edgeShapeAmplitude b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) j p.1 x *
      edgeShapeDenominator b (fun u=>B (u,p.2)) p.1 x^(k-j)
  let DD : (ℝ × E) → ShapeSpace n → ℂ := fun p=>edgeShapeDenominator b (fun u=>B (u,p.2)) p.1
  obtain ⟨hchi,hchi0,hchib,hchis⟩ := edgeShapeCutoff_properties (n:=n) hR'
  have hlim := filtered_edge_shape_cutoff_limit hτ hbalance hmajorant AA DD (edgeShapeCutoff R') 0 hR' hP
    (edge_quadratic_re_pos (hBi eta₀ heta₀) (mul_pos (by norm_num : (0:ℝ)<2) hs))
    (show 0≤M*2^(k-j) by positivity) hc hchi hchi0 hchib hchis ?_ ?_ ?_
  · simp only [zero_mul] at hlim
    apply hlim.congr'
    filter_upwards [htime] with p hp
    congr 1
    unfold edgeLocalJetIntegral
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : edgeShapeCutoff R' x=0
    · simp [hx]
    · have hmem : x∈ball 0 R' := by simpa using hchis x hx
      have hn : DD p x≠0 := by
        intro he
        have hg := hgap p.2 hp.2.2 p.1 hp.1
          (hp.2.1.trans_le ((min_le_right _ _).trans (min_le_left _ _))) x (hangle x hmem)
        change c*(p.1^2+‖x‖^2)≤‖DD p x‖ at hg
        rw [he,norm_zero] at hg
        have hh : 0<c*(p.1^2+‖x‖^2) := mul_pos hc (add_pos_of_pos_of_nonneg (sq_pos_of_pos hp.1) (sq_nonneg _))
        linarith
      have hepow : DD p x^(k+1)=DD p x^(j+1)*DD p x^(k-j) := by
        rw [←pow_add]
        congr 1
        omega
      change (shapeVandermondeSq x:ℂ)*edgeShapeCutoff R' x*
        (edgeShapeAmplitude b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) j p.1 x*(DD p x)^(k-j)) /
          (DD p x)^(k+1) =
        (shapeVandermondeSq x:ℂ)*edgeShapeCutoff R' x*
          edgeShapeAmplitude b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) j p.1 x/(DD p x)^(j+1)
      rw [hepow]
      field_simp
  · filter_upwards [htime] with p hp
    have htR : |p.1|<R := by rw [abs_of_pos hp.1]; exact hp.2.1.trans_le (min_le_left _ _)
    have hh := hlocal p.2 hp.2.2 p.1 htR
    have htsq : p.1^2<r := by
      have hl := hp.2.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [Real.sq_sqrt hr.le,hp.1]
    have hu : ‖Complex.I*(p.1:ℂ)^2‖<r := by simpa using htsq
    have hDu (x : ShapeSpace n) : ‖DD p x‖≤2 := shapeDenominator_norm_le_two_upper hp.1
      (hdata p.2 hp.2.2 _ hu).2.2.1 x
    refine ⟨(hh.1.mul (hh.2.1.pow _)).mono (ball_subset_ball hR'R),
      hh.2.1.mono (ball_subset_ball hR'R),?_,?_⟩
    · intro x hx
      dsimp only [AA]
      rw [norm_mul,norm_pow]
      exact mul_le_mul (hh.2.2 x (ball_subset_ball hR'R hx))
        (pow_le_pow_left₀ (norm_nonneg _) (hDu x) _) (by positivity) hM
    · intro x hx
      exact hgap p.2 hp.2.2 p.1 hp.1
        (hp.2.1.trans_le ((min_le_right _ _).trans (min_le_left _ _))) x (hangle x hx)
  · intro x
    have hh := (family_shapeAmplitude_filtered_limit hτ heta hb (hB eta₀ heta₀)
      (hBi eta₀ heta₀) (hS eta₀ heta₀) (hS0 eta₀ heta₀) j x).mul
      ((family_shapeDenominator_filtered_zero hτ heta hb (hB eta₀ heta₀).continuousAt hres x).pow (k-j))
    simpa only [AA,zero_pow (Nat.sub_pos_of_lt hj).ne',mul_zero] using! hh
  · exact family_shapeDenominator_filtered_limit hτ heta hb (hB eta₀ heta₀).continuousAt hres

end
end IsingBulk.Joint.RegularEdges
