import IsingBulk.Anisotropic.RegularEdges.LeadingIntegral

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- Pure-model integrability is proved from the actual root gap, including the collision point. -/
theorem edgeConstrainedJet_inward_continuousOn {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,ContinuousOn
      (fun q : Fin n→ℝ => edgeConstrainedJet b B S j (Complex.I*(t:ℂ)^2,q)) (edgeCenteredCube n) := by
  obtain ⟨r,hr,hlocal⟩ := Metric.eventually_nhds_iff.mp
    (edgeAngularDensity_jet_near_collision (N := n+1) hb hB hBi hS hS0 j)
  let U : Set (Fin n→ℝ) := {q | ‖edgeFreeShape q‖<min r Real.pi}
  have hU : IsOpen U := isOpen_lt (edgeFreeShape_continuous n).norm continuous_const
  have h0 : (0:Fin n→ℝ)∈U := by simp [U,hr,Real.pi_pos]
  obtain ⟨C,hC,haway⟩ := edgeConstrainedJet_away_bound hb hB hBi hS hS0 hU h0 j
  obtain ⟨c,δ,hc,hδ,hgap⟩ := edgeShapeDenominator_gap (n := n) (b := b) hBi hB.continuousAt
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  let G : ℂ×(Fin n→ℝ)→ℂ×(Fin (n+1)→ℝ) := fun p => (p.1,shapeExtend p.2)
  have hG : Continuous G := by unfold G shapeExtend; fun_prop
  filter_upwards [self_mem_nhdsWithin,htend.eventually haway,
    (eventually_lt_nhds (lt_min zero_lt_one (lt_min hr hδ))).filter_mono nhdsWithin_le_nhds]
    with t ht hawayt htb
  have ht0 : 0<t := ht
  intro q hq
  have hjoint : ContinuousAt (edgeConstrainedJet b B S j) (Complex.I*(t:ℂ)^2,q) := by
    by_cases hqU : q∈U
    · have hshape : ‖edgeFreeShape q‖<min r Real.pi := hqU
      have hnorm : ‖shapeExtend q‖≤‖edgeFreeShape q‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        intro i
        simpa only [edgeFreeShape_apply] using! PiLp.norm_apply_le (edgeFreeShape q).1 i
      have hp : dist (Complex.I*(t:ℂ)^2,shapeExtend q) (0,0)<r := by
        rw [Prod.dist_eq,dist_zero_right,dist_zero_right]
        apply max_lt
        · rw [norm_mul,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
          have ht1 : t<1 := htb.trans_le (min_le_left _ _)
          have htr : t<r := htb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
          nlinarith
        · exact hnorm.trans_lt (hshape.trans_le (min_le_left _ _))
      have hang (i : Fin (n+1)) : (edgeFreeShape q).1 i∈Icc (-Real.pi) Real.pi := by
        have hh := PiLp.norm_apply_le (edgeFreeShape q).1 i
        rw [Real.norm_eq_abs] at hh
        have hz : |(edgeFreeShape q).1 i|<Real.pi := hh.trans_lt (hshape.trans_le (min_le_right _ _))
        exact ⟨(abs_lt.mp hz).1.le,(abs_lt.mp hz).2.le⟩
      have hne : edgeShapeDenominator b B t (edgeFreeShape q)≠0 := by
        intro he
        have hg := hgap t ht0
          (htb.trans_le ((min_le_right _ _).trans (min_le_right _ _))) (edgeFreeShape q) hang
        rw [he,norm_zero] at hg
        have hz : 0<c*(t^2+‖edgeFreeShape q‖^2) := by positivity
        linarith
      have hd := hlocal hp hne
      exact hd.comp (f := G) (x := (Complex.I*(t:ℂ)^2,q)) hG.continuousAt
    · exact (hawayt q (fun i => ⟨hq.1 i,hq.2 i⟩) hqU).1
  exact (hjoint.comp (f := fun q => (Complex.I*(t:ℂ)^2,q)) (x := q)
    (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

theorem edgeConstrainedJet_inward_integrableOn {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,IntegrableOn
      (fun q : Fin n→ℝ => edgeConstrainedJet b B S j (Complex.I*(t:ℂ)^2,q)) (edgeCenteredCube n) := by
  filter_upwards [edgeConstrainedJet_inward_continuousOn (n := n) hb hB hBi hS hS0 j] with t ht
  exact ht.integrableOn_compact (μ := volume) isCompact_Icc

theorem edgeFullDerivativeIntegral_eventually_decomposition {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) {R : ℝ} (hR : 0<R) (hRπ : R≤Real.pi) (j : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2)=
        (Real.sqrt (n+1))⁻¹ • edgeActualLocalDerivativeIntegral (n := n) b B S j R t+
          edgeComplementDerivativeIntegral (n := n) b B S j R (Complex.I*(t:ℂ)^2) := by
  filter_upwards [edgeConstrainedJet_inward_continuousOn (n := n) hb hB hBi hS hS0 j] with t ht
  have hw : Continuous (fun q : Fin n→ℝ => edgeShapeCutoff R (edgeFreeShape q)) :=
    (edgeShapeCutoff_properties (n := n) hR).1.comp (edgeFreeShape_continuous n)
  have hi1 := (hw.continuousOn.mul ht).integrableOn_compact (μ := volume) isCompact_Icc
  have hi2 := (((continuous_const (y := (1:ℂ))).sub hw).continuousOn.mul ht).integrableOn_compact (μ := volume) isCompact_Icc
  rw [←edge_local_derivative_integral_eq b B S hR hRπ t]
  unfold edgeFullDerivativeIntegral edgeComplementDerivativeIntegral
  have hsum := integral_add hi1 hi2
  dsimp only [Pi.mul_apply,Pi.sub_apply] at hsum
  unfold edgeCenteredCube
  rw [←hsum]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  dsimp only
  ring

end
end IsingBulk.Anisotropic.RegularEdges
