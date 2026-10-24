import IsingBulk.Anisotropic.RegularEdges.Numerator

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology

def evenEdgeMajorant (r C M : ℝ) (n : ℕ) : ℝ :=
  M^(2*n)*(matchingCount n:ℝ)*C^n*r^(2*n*(n-1))
def oddEdgeMajorant (r C M : ℝ) (n : ℕ) : ℝ :=
  M^(2*n+1)*(matchingCount (n+1):ℝ)*C^n*r^(2*n*n)

theorem norm_list_product_le {α : Type*} (f : α → ℂ) (xs : List α)
    {M : ℝ} (hM : 0≤M) (hf : ∀ a ∈ xs, ‖f a‖≤M) :
    ‖(xs.map f).prod‖≤M^xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,norm_mul,pow_succ]
    simpa only [mul_comm] using mul_le_mul (hf a (by simp))
      (ih (fun c hc => hf c (by simp [hc]))) (norm_nonneg _) hM

theorem edgeNumerator_norm_uniform {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0)
    (hS : ContinuousAt S 0) (hS0 : S 0≠0) :
    ∃ r C M : ℝ, 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ ∀ᶠ u in 𝓝 (0:ℂ),
      (∀ n qs, qs.length=2*n → (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖edgeNumerator b B S u qs‖≤evenEdgeMajorant r C M n) ∧
      (∀ n qs, qs.length=2*n+1 → (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖edgeNumerator b B S u qs‖≤oddEdgeMajorant r C M n) := by
  obtain ⟨r,C,hr,hr1,hC,hpair⟩ := complete_edge_pairs_uniform hb hB hc
  obtain ⟨M,hM,hone⟩ := edgeOneBody_uniform hb hB hc hS hS0
  refine ⟨r,C,M,hr,hr1,hC,hM,?_⟩
  filter_upwards [hpair,hone] with u hp ho
  constructor
  · intro n qs hlen hqs
    have hh := norm_list_product_le (edgeOneBody b B S u) qs hM.le (fun q hq => ho q (hqs q hq))
    rw [hlen] at hh
    have hx := mul_le_mul (hp.1 n qs hlen hqs) hh (norm_nonneg _) (by positivity)
    simpa only [edgeNumerator,norm_mul,evenEdgeMajorant,mul_assoc,mul_comm,mul_left_comm] using hx
  · intro n qs hlen hqs
    have hh := norm_list_product_le (edgeOneBody b B S u) qs hM.le (fun q hq => ho q (hqs q hq))
    rw [hlen] at hh
    have hx := mul_le_mul (hp.2 n qs hlen hqs) hh (norm_nonneg _) (by positivity)
    simpa only [edgeNumerator,norm_mul,oddEdgeMajorant,mul_assoc,mul_comm,mul_left_comm] using hx

theorem edgeNumerator_eventually_analyticAt {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∀ᶠ u in 𝓝 (0:ℂ), ∀ qs : List ℝ, (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
      AnalyticAt ℂ (fun v => edgeNumerator b B S v qs) u := by
  have hden := radialEdgeRoot_denominator_uniform hb hB hc.continuousAt
  have hden' := (continuousAt_id.prodMk (continuousAt_const (y := (1:ℝ)))).eventually hden
  filter_upwards [hc.eventually_analyticAt,hS.eventually_analyticAt,
    hS.continuousAt.eventually_ne hS0,edgeParamW_uniform_domain hb hB hc.continuousAt,hden'] with u hu hSu hS0u hW hd
  intro qs hqs
  apply edgeNumerator_analyticAt b hu hSu hS0u qs
    (fun q hq => hW q (hqs q hq))
  intro q hq t ht
  simpa only [id_eq,radialEdgeRoot,edgeCircleRoot,radialEdgeY_one,edgeCircleW_unit,edgeParamRoot] using
    hd q (hqs q hq) t (hqs t ht)

/-- Cauchy's estimate is applied only to the analytic numerator. The
singular lattice resolvent is deliberately excluded from this theorem. -/
theorem edgeNumerator_uniform_derivatives {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ δ r C M : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧
      ∀ j : ℕ, ∀ u : ℂ, ‖u‖<δ →
      (∀ n qs, qs.length=2*n → (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖iteratedDeriv j (fun v => edgeNumerator b B S v qs) u‖≤
          (j.factorial:ℝ)*evenEdgeMajorant r C M n/δ^j) ∧
      (∀ n qs, qs.length=2*n+1 → (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖iteratedDeriv j (fun v => edgeNumerator b B S v qs) u‖≤
          (j.factorial:ℝ)*oddEdgeMajorant r C M n/δ^j) := by
  obtain ⟨r,C,M,hr,hr1,hC,hM,hbound⟩ := edgeNumerator_norm_uniform hb hB hc.continuousAt hS.continuousAt hS0
  have ha := edgeNumerator_eventually_analyticAt hb hB hc hS hS0
  have hjoint := hbound.and ha
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hjoint
  refine ⟨ε/3,r,C,M,by positivity,hr,hr1,hC,hM,?_⟩
  intro j u hu
  have hsub : closedBall u (ε/3) ⊆ ball (0:ℂ) ε := by
    intro w hw
    have hwu : dist w u≤ε/3 := hw
    have hu0 : dist u 0<ε/3 := by simpa using hu
    have ht := dist_triangle w u 0
    change dist w 0<ε
    linarith
  have hdiff (qs : List ℝ) (hqs : ∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) :
      DiffContOnCl ℂ (fun v => edgeNumerator b B S v qs) (ball u (ε/3)) := by
    apply DifferentiableOn.diffContOnCl_ball (U := ball (0:ℂ) ε) _ hsub
    intro w hw
    exact ((hball hw).2 qs hqs).differentiableAt.differentiableWithinAt
  constructor
  · intro n qs hlen hqs
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by positivity) (hdiff qs hqs)
    intro w hw
    exact (hball (hsub (sphere_subset_closedBall hw))).1.1 n qs hlen hqs
  · intro n qs hlen hqs
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by positivity) (hdiff qs hqs)
    intro w hw
    exact (hball (hsub (sphere_subset_closedBall hw))).1.2 n qs hlen hqs
end
end IsingBulk.Anisotropic.RegularEdges
