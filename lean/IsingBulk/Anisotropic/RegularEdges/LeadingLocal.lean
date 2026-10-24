import IsingBulk.Anisotropic.RegularEdges.LeadingBounds

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter Metric
open scoped Topology

def edgeShapeCutoff {n : ℕ} (R : ℝ) (x : ShapeSpace n) : ℂ :=
  (max 0 (min 1 (2-4*‖x‖/R)):ℝ)

theorem edgeShapeCutoff_properties {n : ℕ} {R : ℝ} (hR : 0<R) :
    Continuous (@edgeShapeCutoff n R) ∧ edgeShapeCutoff R (0:ShapeSpace n)=1 ∧
    (∀ x : ShapeSpace n,‖edgeShapeCutoff R x‖≤1) ∧
    (∀ x : ShapeSpace n,edgeShapeCutoff R x≠0 → ‖x‖<R) := by
  refine ⟨by unfold edgeShapeCutoff; fun_prop,by simp [edgeShapeCutoff],?_,?_⟩
  · intro x
    rw [edgeShapeCutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (min_le_left _ _)
  · intro x hx
    have hm : max 0 (min 1 (2-4*‖x‖/R))≠0 := Complex.ofReal_ne_zero.mp hx
    have hp : 0<max 0 (min 1 (2-4*‖x‖/R)) := lt_of_le_of_ne (le_max_left _ _) (Ne.symm hm)
    have hi : 0<2-4*‖x‖/R := ((lt_max_iff.mp hp).resolve_left (lt_irrefl 0)).trans_le (min_le_right _ _)
    have hh := (div_lt_iff₀ hR).mp (show 4*‖x‖/R<2 by linarith)
    linarith

theorem edgeShapeCutoff_eq_one {n : ℕ} {R : ℝ} (hR : 0<R) {x : ShapeSpace n}
    (hx : ‖x‖≤R/4) : edgeShapeCutoff R x=1 := by
  have hh : 4*‖x‖/R≤1 := (div_le_iff₀ hR).mpr (by linarith)
  have he : min 1 (2-4*‖x‖/R)=1 := min_eq_left (by linarith)
  simp only [edgeShapeCutoff,he,max_eq_right zero_le_one,Complex.ofReal_one]

def edgeLocalJetIntegral {n : ℕ} (b : ℝ) (B S : ℂ→ℂ) (j : ℕ) (R t : ℝ) : ℂ :=
  ∫ x : ShapeSpace n,(shapeVandermondeSq x:ℂ)*edgeShapeCutoff R x*
    edgeShapeAmplitude b B S j t x/(edgeShapeDenominator b B t x)^(j+1)

/-- A proved local singular limit for the actual analytic jet and actual lattice denominator.
All continuity, scaling and coercivity hypotheses are discharged from the edge model. -/
theorem exists_edgeLocalJetIntegral_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} {B S : ℂ→ℂ} (hb : |b|<1) (hB : AnalyticAt ℂ B 0)
    (hBi : 0<(B 0).im) (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃ R : ℝ,0<R ∧ R≤Real.pi ∧ ∀ R' : ℝ,0<R' → R'≤R →
      Tendsto (fun t : ℝ => (t^a) • edgeLocalJetIntegral (n := n) b B S k R' t)
        (𝓝[>] 0) (𝓝 (edgeAnalyticJet b B S k (0,(0:Fin (n+1)→ℂ))*
          shapePeriodIntrinsic n k ((n+1)/Real.sqrt (1-b^2))
            (-Complex.I*B 0/((2*Real.sqrt (1-b^2):ℝ):ℂ)))) := by
  obtain ⟨R,M,hR,hRπ,hM,hlocal⟩ := edgeShape_local_bounds (n := n) hb hB hBi hS hS0 k
  obtain ⟨c,δ,hc,hδ,hgap⟩ := edgeShapeDenominator_gap (n := n) (b := b) hBi hB.continuousAt
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hQ : 0<(n+1:ℝ)/Real.sqrt (1-b^2) := div_pos (by positivity) hs
  have hw := edge_quadratic_re_pos hBi (mul_pos (by norm_num : (0:ℝ)<2) hs)
  refine ⟨R,hR,hRπ,?_⟩
  intro R' hR' hR'R
  obtain ⟨hchi,hchi0,hchib,hchis⟩ := edgeShapeCutoff_properties (n := n) hR'
  have htR (t : ℝ) (ht : t∈Ioo 0 (min R δ)) : |t|<R := by
    rw [abs_of_pos ht.1]
    exact ht.2.trans_le (min_le_left _ _)
  apply edge_shape_cutoff_limit hbalance hmajorant
    (edgeShapeAmplitude b B S k) (edgeShapeDenominator b B) (edgeShapeCutoff R')
    (edgeAnalyticJet b B S k (0,(0:Fin (n+1)→ℂ)))
    hR' hQ hw hM hc (lt_min hR hδ) hchi hchi0 hchib hchis
  · intro t ht
    exact (hlocal t (htR t ht)).1.mono (ball_subset_ball hR'R)
  · intro t ht
    exact (hlocal t (htR t ht)).2.1.mono (ball_subset_ball hR'R)
  · intro t ht x hx
    exact (hlocal t (htR t ht)).2.2 x (ball_subset_ball hR'R hx)
  · intro t ht x hx
    apply hgap t ht.1 (ht.2.trans_le (min_le_right _ _)) x
    intro i
    have hnorm : ‖x‖<R := (show ‖x‖<R' by simpa using hx).trans_le hR'R
    have hangle := PiLp.norm_apply_le x.1 i
    rw [Real.norm_eq_abs] at hangle
    have hlt : |x.1 i|<Real.pi := hangle.trans_lt (hnorm.trans_le hRπ)
    exact ⟨(abs_lt.mp hlt).1.le,(abs_lt.mp hlt).2.le⟩
  · exact edgeShapeAmplitude_scaled_limit hb hB hBi hS hS0 k
  · exact edgeShapeDenominator_scaled_limit hb hB.continuousAt hres

/-- Even-particle exponent and nonvanishing constant, proved for the actual local jet integral. -/
theorem exists_even_edgeLocalJetIntegral_limit {n k : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*k) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃ R : ℝ,∃ C : ℂ,0<R ∧ R≤Real.pi ∧ C≠0 ∧
      Tendsto (fun t : ℝ => t • edgeLocalJetIntegral (n := n) b B S k R t) (𝓝[>] 0) (𝓝 C) := by
  have hbalance : n+1+(n+1)*n=2*(k+1) := by omega
  obtain ⟨R,hR,hRπ,hlim⟩ := exists_edgeLocalJetIntegral_limit hbalance
    (shapeMajorant_integrable hn hdegree) hb hB hBi hS hS0 hres
  refine ⟨R,_,hR,hRπ,?_,by simpa using hlim R hR le_rfl⟩
  apply mul_ne_zero (edgeAnalyticJet_collision_ne_zero (Nat.succ_pos _) hb hBi hS0 hres k)
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hp := shapePeriod_rightHalfPlane_ne_zero hn hdegree (div_pos (by positivity : 0<(n+1:ℝ)) hs)
    (edge_quadratic_re_pos hBi (mul_pos (by norm_num : (0:ℝ)<2) hs))
  intro he
  rw [shapePeriod_eq_intrinsic] at hp
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,neg_mul] at hp
  rw [he,smul_zero] at hp
  exact hp rfl

end
end IsingBulk.Anisotropic.RegularEdges
