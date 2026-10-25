import IsingBulk.Joint.RegularEdges.FamilyLeadingCutoff
import IsingBulk.Joint.RegularEdges.FamilyLeadingJointLimits
import IsingBulk.Joint.RegularEdges.FamilyFiniteShape

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A single cutoff radius works for all family members, and the local limit is
joint under simultaneous approach of the time and complex family parameters. -/
theorem compact_family_localJet_joint_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃R : ℝ,0<R ∧ R≤Real.pi ∧ ∀R' : ℝ,0<R' → R'≤R → ∀eta₀∈Q,
      Tendsto (fun p : ℝ × E => (p.1^a) • edgeLocalJetIntegral (n:=n)
        b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) k R' p.1)
        (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
        (𝓝 (edgeAnalyticJet (N:=n+1) b (fun u=>B (u,eta₀)) (fun u=>S (u,eta₀)) k (0,0)*
          shapePeriodIntrinsic n k ((n+1)/Real.sqrt (1-b^2))
            (-Complex.I*B (0,eta₀)/((2*Real.sqrt (1-b^2):ℝ):ℂ)))) := by
  obtain ⟨R,M,hR,hRπ,hM,hlocal⟩ := compact_family_shape_local_bounds (n:=n) B S hb hQ hB hBi hS hS0 k
  obtain ⟨c,δ,hc,hδ,hgap⟩ := compact_family_shapeDenominator_gap (n:=n) B hb hQ hB hBi
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
  have htime : ∀ᶠ p : ℝ × E in l, 0<p.1 ∧ p.1<min R δ ∧ p.2∈Q := by
    filter_upwards [self_mem_nhdsWithin,
      (hτ.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (lt_min hR hδ))] with p hp ht
    exact ⟨hp.1,ht,hp.2⟩
  obtain ⟨hchi,hchi0,hchib,hchis⟩ := edgeShapeCutoff_properties (n:=n) hR'
  apply filtered_edge_shape_cutoff_limit hτ hbalance hmajorant
    (fun p : ℝ × E => edgeShapeAmplitude b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) k p.1)
    (fun p : ℝ × E => edgeShapeDenominator b (fun u=>B (u,p.2)) p.1)
    (edgeShapeCutoff R') (edgeAnalyticJet (N:=n+1) b (fun u=>B (u,eta₀))
      (fun u=>S (u,eta₀)) k (0,0)) hR' hP
    (edge_quadratic_re_pos (hBi eta₀ heta₀) (mul_pos (by norm_num) hs)) hM hc
    hchi hchi0 hchib hchis
  · filter_upwards [htime] with p hp
    have htR : |p.1|<R := by rw [abs_of_pos hp.1]; exact hp.2.1.trans_le (min_le_left _ _)
    have hh := hlocal p.2 hp.2.2 p.1 htR
    refine ⟨hh.1.mono (ball_subset_ball hR'R),hh.2.1.mono (ball_subset_ball hR'R),
      fun x hx=>hh.2.2 x (ball_subset_ball hR'R hx),?_⟩
    intro x hx
    apply hgap p.2 hp.2.2 p.1 hp.1 (hp.2.1.trans_le (min_le_right _ _)) x
    intro i
    have hnorm : ‖x‖<R := (show ‖x‖<R' by simpa using hx).trans_le hR'R
    have hangle := PiLp.norm_apply_le x.1 i
    rw [Real.norm_eq_abs] at hangle
    have hlt : |x.1 i|<Real.pi := hangle.trans_lt (hnorm.trans_le hRπ)
    exact ⟨(abs_lt.mp hlt).1.le,(abs_lt.mp hlt).2.le⟩
  · exact family_shapeAmplitude_filtered_limit hτ heta hb (hB eta₀ heta₀)
      (hBi eta₀ heta₀) (hS eta₀ heta₀) (hS0 eta₀ heta₀) k
  · exact family_shapeDenominator_filtered_limit hτ heta hb (hB eta₀ heta₀).continuousAt hres

end
end IsingBulk.Joint.RegularEdges
