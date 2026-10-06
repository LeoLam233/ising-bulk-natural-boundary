import IsingBulk.First.JointPoleRegularity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform parameter-derivative bounds on a fixed regular compact tube.
The tube radius is selected before the derivative order. -/
namespace IsingBulk.First
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def meanParameterIter (F : ℂ × E → ℂ) : ℕ → ℂ × E → ℂ
  | 0 => F
  | j+1 => parameterDeriv (meanParameterIter F j)

theorem meanParameterIter_analyticAt {F : ℂ × E → ℂ} {p : ℂ × E}
    (hF : AnalyticAt ℂ F p) (j : ℕ) : AnalyticAt ℂ (meanParameterIter F j) p := by
  induction j with
  | zero => exact hF
  | succ j ih => exact parameterDeriv_analyticAt ih

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem meanParameterIter_eq_iteratedDeriv (F : ℂ × E → ℂ) (j : ℕ) (s : ℂ) (u : E) :
    meanParameterIter F j (s,u) = (deriv^[j] (fun z => F (z,u))) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    change deriv (fun z => meanParameterIter F j (z,u)) s = _
    rw [show (fun z => meanParameterIter F j (z,u)) = deriv^[j] (fun z => F (z,u)) from funext ih]
    rw [Function.iterate_succ',Function.comp_apply]

/-- A fixed tube of actual analyticity gives uniform bounds for every fixed
parameter-derivative order, without order-dependent shrinking of shape support. -/
theorem compact_analytic_parameter_tube
    {P X : Type*} [NormedAddCommGroup P] [ProperSpace P]
    [TopologicalSpace X] [T2Space X] {K : Set X} (hK : IsCompact K)
    (F : ℂ × E → ℂ) (g : P × X → ℂ × E) (hg : Continuous g) (p₀ : P)
    (hbase : ∀ x ∈ K, AnalyticAt ℂ F (g (p₀,x))) :
    ∃ r : ℝ, 0 < r ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ p : P, ‖p-p₀‖ ≤ r → ∀ x ∈ K, ‖meanParameterIter F j (g (p,x))‖ ≤ C := by
  let U : Set (P × X) := g ⁻¹' {q | AnalyticAt ℂ F q}
  have hU : IsOpen U := (isOpen_analyticAt ℂ F).preimage hg
  have hsub : ({p₀} : Set P) ×ˢ K ⊆ U := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    have hp' : p=p₀ := mem_singleton_iff.mp hp
    subst p
    exact hbase x hx
  obtain ⟨V,W,hVo,_hWo,hpV,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hU hsub
  have hVmem : V ∈ 𝓝 p₀ := hVo.mem_nhds (hpV (mem_singleton p₀))
  obtain ⟨eta,heta,hball⟩ := Metric.mem_nhds_iff.mp hVmem
  let r := eta/2
  have hr : 0 < r := half_pos heta
  have hreg (p : P) (hp : p ∈ closedBall p₀ r) (x : X) (hx : x ∈ K) :
      AnalyticAt ℂ F (g (p,x)) := by
    apply hVW ⟨hball ?_,hKW hx⟩
    have hd := mem_closedBall.mp hp
    dsimp [r] at hd
    exact (lt_of_le_of_lt hd (by linarith))
  refine ⟨r,hr,?_⟩
  intro j
  have hcont : ContinuousOn (fun q : P × X => meanParameterIter F j (g q)) (closedBall p₀ r ×ˢ K) := by
    intro q hq
    exact ((meanParameterIter_analyticAt (hreg q.1 hq.1 q.2 hq.2) j).continuousAt.comp hg.continuousAt).continuousWithinAt
  obtain ⟨M,hM⟩ := ((isCompact_closedBall p₀ r).prod hK).exists_bound_of_continuousOn hcont
  refine ⟨max M 0+1,by positivity,?_⟩
  intro p hp x hx
  have hpmem : p ∈ closedBall p₀ r := by simpa [mem_closedBall,dist_eq_norm] using hp
  exact (hM (p,x) ⟨hpmem,hx⟩).trans (by linarith [le_max_left M 0])

end
end IsingBulk.First
