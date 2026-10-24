import IsingBulk.Anisotropic.RegularEdges.LeadingLocal

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter Metric
open scoped Topology

/-- In one fixed neighborhood all local rational jet identities are actual derivatives. -/
theorem edgeShape_derivative_neighborhood {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ r : ℝ,0<r ∧ ∀ t : ℝ,|t|<r → ∀ x : ShapeSpace n,‖x‖<r →
      edgeShapeDenominator b B t x≠0 → ∀ j : ℕ,
      iteratedDeriv j (fun u => edgeAngularDensity b B S u (fun i => x.1 i)) (Complex.I*(t:ℂ)^2)=
        (shapeVandermondeSq x:ℂ)*edgeShapeAmplitude b B S j t x/
          edgeShapeDenominator b B t x^(j+1) := by
  let G : ℝ×ShapeSpace n→ℂ×(Fin (n+1)→ℂ) := fun p =>
    (Complex.I*(p.1:ℂ)^2,fun i => (p.2.1 i:ℂ))
  have hG : Continuous G := by unfold G; fun_prop
  have hG0 : G 0=0 := by ext <;> simp [G]
  have ht : Tendsto G (𝓝 0) (𝓝 0) := hG0 ▸ hG.tendsto 0
  have hA := edgeComplexAmplitude_analyticAt (N := n+1) hb hB hBi hS hS0
  have hD := edgeComplexDenominator_analyticAt (N := n+1) hb hB
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    (ht.eventually (hA.eventually_analyticAt.and hD.eventually_analyticAt))
  refine ⟨r,hr,?_⟩
  intro t htr x hxr hne j
  have hp : dist (t,x) 0<r := by
    rw [dist_zero_right,Prod.norm_def,Real.norm_eq_abs]
    exact max_lt htr hxr
  obtain ⟨ha,hd⟩ := hball hp
  have hu : AnalyticAt ℂ (fun u : ℂ => (u,fun i : Fin (n+1) => (x.1 i:ℂ))) (Complex.I*(t:ℂ)^2) :=
    analyticAt_id.prod analyticAt_const
  have hh := edgeAngularDensity_iteratedDeriv b B S (fun i => x.1 i) (Complex.I*(t:ℂ)^2) j
    (ha.comp (f := fun u : ℂ => (u,fun i : Fin (n+1) => (x.1 i:ℂ))) (x := Complex.I*(t:ℂ)^2) hu)
    (hd.comp (f := fun u : ℂ => (u,fun i : Fin (n+1) => (x.1 i:ℂ))) (x := Complex.I*(t:ℂ)^2) hu) hne
  simpa only [shapeVandermondeSq,Complex.ofReal_pow,edgeShapeAmplitude,edgeShapeDenominator,mul_assoc] using hh

def edgeActualLocalDerivativeIntegral {n : ℕ} (b : ℝ) (B S : ℂ→ℂ) (j : ℕ) (R t : ℝ) : ℂ :=
  ∫ x : ShapeSpace n,edgeShapeCutoff R x*
    iteratedDeriv j (fun u => edgeAngularDensity b B S u (fun i => x.1 i)) (Complex.I*(t:ℂ)^2)

/-- The comparison is with literal iterated derivatives of the complete local angular density. -/
theorem edgeActualLocalDerivativeIntegral_eventually_eq {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ r : ℝ,0<r ∧ ∀ R : ℝ,0<R → R≤r → ∀ j : ℕ,
      ∀ᶠ t : ℝ in 𝓝[>] 0,edgeActualLocalDerivativeIntegral (n := n) b B S j R t=
        edgeLocalJetIntegral (n := n) b B S j R t := by
  obtain ⟨r,hr,hid⟩ := edgeShape_derivative_neighborhood (n := n) hb hB hBi hS hS0
  obtain ⟨c,δ,hc,hδ,hgap⟩ := edgeShapeDenominator_gap (n := n) (b := b) hBi hB.continuousAt
  refine ⟨min r Real.pi,lt_min hr Real.pi_pos,?_⟩
  intro R hR hRr j
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (lt_min hr hδ)).filter_mono nhdsWithin_le_nhds] with t ht htbound
  have ht0 : 0<t := ht
  have htr : |t|<r := by rw [abs_of_pos ht0]; exact htbound.trans_le (min_le_left _ _)
  unfold edgeActualLocalDerivativeIntegral edgeLocalJetIntegral
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : edgeShapeCutoff R x=0
  · simp [hx]
  · have hxr := (edgeShapeCutoff_properties (n := n) hR).2.2.2 x hx
    have hangle (i : Fin (n+1)) : x.1 i∈Icc (-Real.pi) Real.pi := by
      have hh := PiLp.norm_apply_le x.1 i
      rw [Real.norm_eq_abs] at hh
      have hl : |x.1 i|<Real.pi := hh.trans_lt (hxr.trans_le (hRr.trans (min_le_right _ _)))
      exact ⟨(abs_lt.mp hl).1.le,(abs_lt.mp hl).2.le⟩
    have hn : edgeShapeDenominator b B t x≠0 := by
      intro he
      have hg := hgap t ht0 (htbound.trans_le (min_le_right _ _)) x hangle
      rw [he,norm_zero] at hg
      have hp : 0<c*(t^2+‖x‖^2) := mul_pos hc (add_pos_of_pos_of_nonneg (sq_pos_of_pos ht0) (sq_nonneg _))
      linarith
    rw [hid t htr x (hxr.trans_le (hRr.trans (min_le_left _ _))) hn j]
    ring

end
end IsingBulk.Anisotropic.RegularEdges
