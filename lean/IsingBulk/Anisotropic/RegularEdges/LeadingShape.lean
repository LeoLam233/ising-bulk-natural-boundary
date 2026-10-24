import IsingBulk.Anisotropic.RegularEdges.LeadingScaling
import IsingBulk.Anisotropic.RegularEdges.LeadingCutoff

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter
open scoped Topology BigOperators

def edgeShapeAmplitude {n : ℕ} (b : ℝ) (B S : ℂ→ℂ) (j : ℕ) (t : ℝ) (x : ShapeSpace n) : ℂ :=
  edgeSincFactor (fun i => x.1 i)*edgeAnalyticJet b B S j (Complex.I*(t:ℂ)^2,fun i => (x.1 i:ℂ))
def edgeShapeDenominator {n : ℕ} (b : ℝ) (B : ℂ→ℂ) (t : ℝ) (x : ShapeSpace n) : ℂ :=
  edgeComplexDenominator b B (Complex.I*(t:ℂ)^2,fun i => (x.1 i:ℂ))

theorem shape_sup_norm_sq_le {n : ℕ} (x : ShapeSpace n) :
    ‖x‖^2≤(n+1:ℝ)*‖fun i => x.1 i‖^2 := by
  change ‖x.1‖^2≤_
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i,(x.1 i)^2≤∑ _i : Fin (n+1),‖fun j => x.1 j‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := norm_le_pi_norm (fun j => x.1 j) i
      rw [Real.norm_eq_abs] at h
      nlinarith [sq_abs (x.1 i),abs_nonneg (x.1 i),norm_nonneg (fun j => x.1 j)]
    _ = _ := by simp

/-- The actual finite-particle product gap controls the intrinsic Euclidean shape norm. -/
theorem edgeShapeDenominator_gap {n : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hBi : 0<(B 0).im) (hB : ContinuousAt B 0) :
    ∃ c δ : ℝ,0<c ∧ 0<δ ∧ ∀ t : ℝ,0<t → t<δ → ∀ x : ShapeSpace n,
      (∀ i,x.1 i∈Icc (-Real.pi) Real.pi) →
      c*(t^2+‖x‖^2)≤‖edgeShapeDenominator b B t x‖ := by
  obtain ⟨c,δ,hc,hδ,hgap⟩ := edgeRootProduct_retained_gap (b := b) hBi hB
  have hNp : 0<(n+1:ℝ) := by positivity
  have hN0 : (n+1:ℝ)≠0 := ne_of_gt hNp
  refine ⟨c/(n+1),Real.sqrt δ,div_pos hc hNp,Real.sqrt_pos.mpr hδ,?_⟩
  intro t ht htδ x hx
  have htsq : t^2<δ := by nlinarith [Real.sq_sqrt hδ.le]
  have hg := (hgap (t^2) (sq_pos_of_pos ht) htsq (n+1) (n+1)
    (fun i => x.1 i) id hx).2.2
  have hs := shape_sup_norm_sq_le x
  have hineq : t^2+‖x‖^2≤(n+1:ℝ)*(t^2+‖fun i => x.1 i‖^2) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ) by positivity) (sq_nonneg t)]
  calc
    c/(n+1)*(t^2+‖x‖^2)≤c/(n+1)*((n+1)*(t^2+‖fun i => x.1 i‖^2)) :=
      mul_le_mul_of_nonneg_left hineq (div_nonneg hc.le hNp.le)
    _ = c*(t^2+‖fun i => x.1 i‖^2) := by field_simp
    _ ≤ _ := by
      simpa only [edgeShapeDenominator,edgeComplexDenominator,edgeComplexRoot_real,
        edgeRootProduct,Complex.ofReal_pow,id_eq] using hg

theorem edgeShapeAmplitude_scaled_limit {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) (x : ShapeSpace n) :
    Tendsto (fun t : ℝ => edgeShapeAmplitude b B S j t (t • x)) (𝓝[>] 0)
      (𝓝 (edgeAnalyticJet b B S j (0,(0:Fin (n+1)→ℂ)))) := by
  have hs : Tendsto (fun t : ℝ => edgeSincFactor (fun i => t*x.1 i)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : Continuous (fun t : ℝ => edgeSincFactor (fun i => t*x.1 i)) :=
      (edgeSincFactor_continuous (n+1)).comp (by fun_prop)
    simpa [edgeSincFactor] using! (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa [edgeShapeAmplitude] using! hs.mul (edgeAnalyticJet_scaled_limit hb hB hBi hS hS0 j (fun i => x.1 i))

theorem edgeShapeDenominator_scaled_limit {n : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : ContinuousAt B 0) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (x : ShapeSpace n) :
    Tendsto (fun t : ℝ => edgeShapeDenominator b B t (t • x)/(t:ℂ)^2) (𝓝[>] 0)
      (𝓝 (((n+1:ℝ)/Real.sqrt (1-b^2):ℝ)+
        (-Complex.I*B 0/((2*Real.sqrt (1-b^2):ℝ):ℂ))*(‖x‖:ℂ)^2)) := by
  have hs : (∑ i,(x.1 i:ℂ)^2)=(‖x‖:ℂ)^2 := by
    simp_rw [←Complex.ofReal_pow]
    rw [←Complex.ofReal_sum]
    congr 1
    exact (EuclideanSpace.real_norm_sq_eq x.1).symm
  have h := edgeRootProduct_scaled_denominator_limit hb hB (fun i => x.1 i) hres
  rw [hs] at h
  convert! h using 1
  · ext t
    simp [edgeShapeDenominator,edgeComplexDenominator,edgeComplexRoot,edgeParamRoot,edgeParamW,
      edgeRootProduct,Complex.ofReal_cos]
  · congr 1
    push_cast
    ring

end
end IsingBulk.Anisotropic.RegularEdges
