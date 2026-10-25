import IsingBulk.Joint.FormFactors.NormalSeries

/-! # A full Frechet Cauchy estimate on one fixed inner ball
The bound controls every mixed derivative, not just derivatives along a chosen
curve. The inner ball is independent of derivative order.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem norm_iteratedFDeriv_le_of_expanded_ball (k : ℕ) {f : E → G} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) {x : E} {ε M : ℝ}
    (hε : 0<ε) (hM : 0≤M)
    (hball : closedBall x (((k+1:ℕ):ℝ)*ε)⊆U)
    (hb : ∀ y∈closedBall x (((k+1:ℕ):ℝ)*ε), ‖f y‖≤M) :
    ‖iteratedFDeriv ℂ k f x‖≤M/ε^k := by
  induction k generalizing x with
  | zero =>
    simpa using hb x (mem_closedBall_self (by positivity))
  | succ k ih =>
    have hrad : ε≤((k+1+1:ℕ):ℝ)*ε := by
      have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
      push_cast
      nlinarith
    have hsmall : closedBall x ε⊆U :=
      (closedBall_subset_closedBall hrad).trans hball
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ k f) U := by
      intro y hy
      exact ((show ContDiffAt ℂ (1+k) f y from (hf y hy).contDiffAt).iteratedFDeriv_right
        (m := 1) (by simp)).differentiableAt_one.differentiableWithinAt
    have hbound : ∀ y∈closedBall x ε, ‖iteratedFDeriv ℂ k f y‖≤M/ε^k := by
      intro y hy
      have hsub : closedBall y (((k+1:ℕ):ℝ)*ε)⊆closedBall x (((k+1+1:ℕ):ℝ)*ε) := by
        intro z hz
        have ht := dist_triangle z y x
        have hy' : dist y x≤ε := hy
        have hz' : dist z y≤((k+1:ℕ):ℝ)*ε := hz
        change dist z x≤((k+1+1:ℕ):ℝ)*ε
        push_cast at hz' ⊢
        nlinarith
      exact ih (hsub.trans hball) (fun z hz => hb z (hsub hz))
    have hc := FormFactors.norm_fderiv_le_of_ball_bound hU hdiff hε hsmall
      (div_nonneg hM (pow_nonneg hε.le _)) hbound
    simpa only [norm_fderiv_iteratedFDeriv,div_div,←pow_succ] using hc

/-- One fixed half-ball works for every derivative order and all multilinear
mixed directions. The constants are explicit and independent of the function. -/
theorem norm_iteratedFDeriv_le_on_half_ball (k : ℕ) {f : E → G} {a x : E} {δ M : ℝ}
    (hδ : 0<δ) (hM : 0≤M) (hf : AnalyticOnNhd ℂ f (ball a δ))
    (hb : ∀ y∈ball a δ, ‖f y‖≤M) (hx : x∈ball a (δ/2)) :
    ‖iteratedFDeriv ℂ k f x‖≤M/(δ/(2*((k+1:ℕ):ℝ)))^k := by
  let ε := δ/(2*((k+1:ℕ):ℝ))
  have hε : 0<ε := by dsimp [ε]; positivity
  have he : ((k+1:ℕ):ℝ)*ε=δ/2 := by dsimp [ε]; field_simp
  have hball : closedBall x (((k+1:ℕ):ℝ)*ε)⊆ball a δ := by
    rw [he]
    intro y hy
    have ht := dist_triangle y x a
    have hy' : dist y x≤δ/2 := hy
    have hx' : dist x a<δ/2 := hx
    change dist y a<δ
    linarith
  exact norm_iteratedFDeriv_le_of_expanded_ball k isOpen_ball hf hε hM hball
    (fun y hy => hb y (hball hy))

end
end IsingBulk.Joint.RegularEdges
