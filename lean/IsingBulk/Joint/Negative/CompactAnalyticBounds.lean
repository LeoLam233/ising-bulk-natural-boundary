import IsingBulk.Joint.Negative.CompactFamilies
import IsingBulk.First.CompactAnalyticShapeIntegral

/-! Common scalar bounds, including every fixed derivative, on compact
complex-parameter families. Constants are chosen only after the derivative
order, but before the family member and particle number. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First

variable {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A compact analytic family has a common transverse neighborhood and bound.
This works in arbitrary complex normed parameter spaces. -/
theorem compact_analytic_uniform_bound (f : X × E → F) {K : Set E}
    (hK : IsCompact K) (hf : ∀ eta ∈ K, AnalyticAt ℂ f (0, eta)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ eta ∈ K, ∀ x : X, ‖x‖ < r →
      AnalyticAt ℂ f (x, eta) ∧ ‖f (x, eta)‖ < M := by
  have hcont : ContinuousOn (fun eta => f (0, eta)) K := by
    intro eta heta
    exact ((hf eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  let M := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right C 0]
  let U : Set (X × E) := {q | AnalyticAt ℂ f q ∧ ‖f q‖ < M}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and
      (hq.1.continuousAt.norm.eventually_lt continuousAt_const hq.2)
  obtain ⟨r, hr, htube⟩ := compact_product_tube hK hU (by
    intro eta heta
    refine ⟨hf eta heta, ?_⟩
    dsimp [M]
    linarith [hC eta heta, le_max_left C 0])
  exact ⟨r, M, hr, hM, htube⟩

/-- A joint derivative remains jointly analytic on the compact complex family.
The resulting bound is a common bound, not one obtained separately for eta. -/
theorem compact_parameter_jet_uniform_bound (f : ℂ × E → ℂ) {K : Set E}
    (hK : IsCompact K) (hf : ∀ eta ∈ K, AnalyticAt ℂ f (0, eta)) (k : ℕ) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ eta ∈ K, ∀ t : ℂ, ‖t‖ < r →
      AnalyticAt ℂ (jointParameterJet f k) (t, eta) ∧
        ‖iteratedDeriv k (fun u => f (u, eta)) t‖ < M := by
  obtain ⟨r, M, hr, hM, hbound⟩ := compact_analytic_uniform_bound
    (jointParameterJet f k) hK (fun eta heta => jointParameterJet_analyticAt (hf eta heta) k)
  refine ⟨r, M, hr, hM, ?_⟩
  intro eta heta t ht
  simpa only [jointParameterJet_eq, iteratedDeriv_eq_iterate] using hbound eta heta t ht

/-- A derivative bound on the compact product gives a common Lipschitz
constant in all scalar variables; the family parameter remains complex. -/
theorem compact_analytic_uniform_lipschitz (f : X × E→F) {K : Set E}
    (hK : IsCompact K) (hf : ∀eta∈K,AnalyticAt ℂ f (0,eta)) :
    ∃r L M : ℝ,0<r ∧ 0<L ∧ 0<M ∧
      (∀eta∈K,∀x : X,‖x‖<r → AnalyticAt ℂ f (x,eta) ∧ ‖f (x,eta)‖≤M) ∧
      (∀eta∈K,∀x y : X,‖x‖<r → ‖y‖<r → ‖f (x,eta)-f (y,eta)‖≤L*‖x-y‖) := by
  obtain ⟨r0,M,hr0,hM,hbound⟩ := compact_analytic_uniform_bound f hK hf
  obtain ⟨r1,L,hr1,hL,hderiv⟩ := compact_analytic_uniform_bound (fderiv ℂ f) hK
    (fun eta heta=>(hf eta heta).fderiv)
  let r := min r0 r1
  have hr : 0<r := lt_min hr0 hr1
  refine ⟨r,L,M,hr,hL,hM,?_,?_⟩
  · intro eta heta x hx
    have hh := hbound eta heta x (hx.trans_le (min_le_left _ _))
    exact ⟨hh.1,hh.2.le⟩
  · intro eta heta x y hx hy
    have hcv : Convex ℝ (ball (0:X) r ×ˢ ({eta}:Set E)) :=
      (convex_ball _ _).prod (convex_singleton eta)
    have hh := hcv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun q hq=>by
        rcases q with ⟨x,e⟩
        have he : e=eta := mem_singleton_iff.mp hq.2
        subst e
        have hx : ‖x‖<r := by simpa using hq.1
        exact (hbound eta heta x (hx.trans_le (min_le_left _ _))).1.differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      (fun q hq=>by
        have hqe : q.2=eta := mem_singleton_iff.mp hq.2
        have hqx : ‖q.1‖<r := by simpa using hq.1
        have hb := (hderiv eta heta q.1 (hqx.trans_le (min_le_right _ _))).2.le
        simpa only [←hqe] using hb)
      (show (y,eta)∈ball (0:X) r ×ˢ ({eta}:Set E) by exact ⟨by simpa using hy,rfl⟩)
      (show (x,eta)∈ball (0:X) r ×ˢ ({eta}:Set E) by exact ⟨by simpa using hx,rfl⟩)
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
      max_eq_left (norm_nonneg (x-y))] using hh

end
end IsingBulk.Joint.Negative