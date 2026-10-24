import IsingBulk.Anisotropic.RegularEdges.LeadingShape

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter Metric
open scoped Topology

private theorem local_bound_of_eventually_continuous {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : E→F}
    (h : ∀ᶠ p in 𝓝 (0:E),ContinuousAt f p) :
    ∃ r M : ℝ,0<r ∧ 0≤M ∧ ContinuousOn f (ball 0 r) ∧ ∀ p∈ball 0 r,‖f p‖≤M := by
  have h0 : ContinuousAt f 0 := mem_of_mem_nhds h
  have hb : ∀ᶠ p in 𝓝 (0:E),‖f p‖<‖f 0‖+1 :=
    h0.norm.eventually_lt continuousAt_const (by linarith)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (h.and hb)
  refine ⟨r,‖f 0‖+1,hr,by positivity,?_,?_⟩
  · intro p hp
    exact (hball hp).1.continuousWithinAt
  · intro p hp
    exact (hball hp).2.le

/-- The local bounds are derived from the genuine jointly analytic derivative numerator. -/
theorem edgeShape_local_bounds {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ R M : ℝ,0<R ∧ R≤Real.pi ∧ 0≤M ∧ ∀ t : ℝ,|t|<R →
      ContinuousOn (edgeShapeAmplitude (n := n) b B S j t) (ball 0 R) ∧
      ContinuousOn (edgeShapeDenominator (n := n) b B t) (ball 0 R) ∧
      ∀ x : ShapeSpace n,x∈ball 0 R →‖edgeShapeAmplitude b B S j t x‖≤M := by
  let G : ℝ×ShapeSpace n→ℂ×(Fin (n+1)→ℂ) := fun p =>
    (Complex.I*(p.1:ℂ)^2,fun i => (p.2.1 i:ℂ))
  have hG : Continuous G := by unfold G; fun_prop
  have hG0 : G 0=0 := by ext <;> simp [G]
  have ht : Tendsto G (𝓝 0) (𝓝 0) := hG0 ▸ hG.tendsto 0
  have hJ := edgeAnalyticJet_analyticAt (N := n+1) hb hB hBi hS hS0 j
  have hD := edgeComplexDenominator_analyticAt (N := n+1) hb hB
  have hsinc : Continuous (fun p : ℝ×ShapeSpace n => edgeSincFactor (fun i => p.2.1 i)) :=
    (edgeSincFactor_continuous (n+1)).comp (by fun_prop)
  let F : ℝ×ShapeSpace n→ℂ × ℂ := fun p =>
    (edgeShapeAmplitude b B S j p.1 p.2,edgeShapeDenominator b B p.1 p.2)
  have hev : ∀ᶠ p in 𝓝 (0:ℝ×ShapeSpace n),ContinuousAt F p := by
    filter_upwards [ht.eventually hJ.eventually_analyticAt,ht.eventually hD.eventually_analyticAt] with p hj hd
    exact (hsinc.continuousAt.mul (hj.continuousAt.comp hG.continuousAt)).prodMk
      (hd.continuousAt.comp hG.continuousAt)
  obtain ⟨r,M,hr,hM,hc,hbound⟩ := local_bound_of_eventually_continuous hev
  let R := min r Real.pi
  have hR : 0<R := lt_min hr Real.pi_pos
  have hRr : R≤r := min_le_left _ _
  refine ⟨R,M,hR,min_le_right _ _,hM,?_⟩
  intro t htR
  have hmap : MapsTo (fun x : ShapeSpace n => (t,x)) (ball 0 R) (ball 0 r) := by
    intro x hx
    have hx' : ‖x‖<R := by simpa using hx
    have ht' : ‖t‖<R := by simpa [Real.norm_eq_abs] using htR
    change dist (t,x) 0<r
    rw [dist_zero_right,Prod.norm_def]
    exact (max_lt ht' hx').trans_le hRr
  have hct := hc.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  refine ⟨hct.fst,hct.snd,?_⟩
  intro x hx
  exact (norm_fst_le (F (t,x))).trans (hbound (t,x) (hmap hx))

end
end IsingBulk.Anisotropic.RegularEdges
