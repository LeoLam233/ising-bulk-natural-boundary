import IsingBulk.Joint.RegularEdges.FamilyFiniteAnalytic

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A common retained root gap for the actual variable-anisotropy family. -/
theorem compact_family_root_gap {b : ℝ} (B : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im) :
    ∃ δ c : ℝ,0<δ ∧ 0<c ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im →
      ∀q∈Icc (-Real.pi) Real.pi,
        c*(u.im+q^2)≤1-‖edgeParamRoot b (fun u=>B (u,eta)) u q‖ := by
  let f : E → ℂ × ℂ := fun eta => (B (0,eta),1)
  have hf : ContinuousOn f Q := by
    intro eta heta
    exact (((hB eta heta).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).prodMk continuousAt_const).continuousWithinAt
  have hK := hQ.image_of_continuousOn hf
  obtain ⟨r,c,hr,hc,hgap⟩ := compact_roots_polydisks hb hK
    (by rintro v ⟨eta,heta,rfl⟩; exact hBi eta heta)
    (by rintro v ⟨eta,heta,rfl⟩; exact one_ne_zero)
  have he : ∀ᶠu : ℂ in 𝓝 0,∀eta∈Q,
      (u,(B (u,eta),1))∈ball ((0:ℂ),f eta) r := by
    apply hQ.eventually_forall_of_forall_eventually
    intro eta heta
    have hcent : ContinuousAt (fun x : ℂ × E => B (0,x.2)) (0,eta) :=
      (hB eta heta).continuousAt.comp (f:=fun x : ℂ × E => ((0:ℂ),x.2)) (x:=(0,eta)) (continuousAt_const.prodMk continuousAt_snd)
    have hl : ContinuousAt (fun x : ℂ × E => (x.1,(B x,(1:ℂ)))) (0,eta) :=
      continuousAt_fst.prodMk ((hB eta heta).continuousAt.prodMk continuousAt_const)
    have hright : ContinuousAt (fun x : ℂ × E => ((0:ℂ),(B (0,x.2),(1:ℂ)))) (0,eta) :=
      continuousAt_const.prodMk (hcent.prodMk continuousAt_const)
    have hdist : ContinuousAt (fun x : ℂ × E =>
        dist (x.1,(B x,(1:ℂ))) ((0:ℂ),(B (0,x.2),(1:ℂ)))) (0,eta) :=
      hl.dist hright
    exact hdist.eventually_lt_const (by simpa using hr)
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,c,hδ,hc,?_⟩
  intro eta heta u hu hi q hq
  exact (hgap (f eta) (mem_image_of_mem f heta)).2 q hq |>.2.2 _
    (hδb (by simpa using hu) eta heta) hi

/-- The common finite-dimensional product gap controls the true Euclidean
shape norm, including arbitrarily small positive t. -/
theorem compact_family_shapeDenominator_gap {n : ℕ} {b : ℝ} (B : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im) :
    ∃ c δ : ℝ,0<c ∧ 0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ∀x : ShapeSpace n,
      (∀i,x.1 i∈Icc (-Real.pi) Real.pi) →
      c*(t^2+‖x‖^2)≤‖edgeShapeDenominator b (fun u=>B (u,eta)) t x‖ := by
  obtain ⟨δ,c,hδ,hc,hgap⟩ := compact_family_root_gap B hb hQ hB hBi
  have hNp : 0<(n+1:ℝ) := by positivity
  have hN0 : (n+1:ℝ)≠0 := ne_of_gt hNp
  refine ⟨c/(n+1),Real.sqrt δ,div_pos hc hNp,Real.sqrt_pos.mpr hδ,?_⟩
  intro eta heta t ht htδ x hx
  have htsq : t^2<δ := by nlinarith [Real.sq_sqrt hδ.le]
  have hu : ‖Complex.I*(t:ℂ)^2‖<δ := by simpa using htsq
  have him : (Complex.I*(t:ℂ)^2).im=t^2 := by simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
  have hi : 0<(Complex.I*(t:ℂ)^2).im := by rw [him]; positivity
  have hg := root_product_retained_gap
    (fun i => edgeParamRoot b (fun u=>B (u,eta)) (Complex.I*(t:ℂ)^2) (x.1 i))
    (fun i => x.1 i) (id : Fin (n+1)→Fin (n+1)) hc hi
    (fun i => hgap eta heta _ hu hi _ (hx i))
  rw [him] at hg
  have hs := shape_sup_norm_sq_le x
  have hineq : t^2+‖x‖^2≤(n+1:ℝ)*(t^2+‖fun i => x.1 i‖^2) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ) by positivity) (sq_nonneg t)]
  calc
    c/(n+1)*(t^2+‖x‖^2)≤c/(n+1)*((n+1)*(t^2+‖fun i => x.1 i‖^2)) :=
      mul_le_mul_of_nonneg_left hineq (div_nonneg hc.le hNp.le)
    _ = c*(t^2+‖fun i => x.1 i‖^2) := by field_simp
    _ ≤ _ := by
      simpa [edgeShapeDenominator,edgeComplexDenominator,edgeComplexRoot_real,id_eq] using hg.2.2

end
end IsingBulk.Joint.RegularEdges
