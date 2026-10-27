import IsingBulk.Preferred22.CompactRadialIntegral

/-! The radial FTC passage packaged as the proved uniform-limit theorem
for derivatives. Actual shell and flux estimates enter through their
quantitative logarithmic geometric errors on positive radial intervals. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped Topology

/-- A common numerical norm error tending to zero gives uniform
convergence on the exact stated set. -/
theorem preferred_uniform_limit_of_norm_bound {S : Set ℝ}
    (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ m x,x∈S → ‖F m x-G x‖≤b m) :
    TendstoUniformlyOn F G atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb.eventually (Iio_mem_nhds hε)] with m hm x hx
  rw [dist_eq_norm,norm_sub_rev]
  exact (hbound m x hx).trans_lt hm

/-- Differentiation commutes with the actual puncture exhaustion once the
function and derivative errors have the proved geometric logarithmic size.
The proof uses uniform convergence only on a compact positive radial
neighborhood of the evaluation point. -/
theorem preferred_hasDerivAt_of_log_geometric_approximants
    (F F' : ℕ → ℝ → ℂ) (G G' : ℝ → ℂ)
    {ε₀ ρ A B : ℝ} (hρ : 0≤ρ) (hρ1 : ρ<1) (hA : 0≤A) (hB : 0≤B)
    (hderiv : ∀ m ε,ε∈Ioo 0 ε₀ → HasDerivAt (F m) (F' m ε) ε)
    (hvalue : ∀ m ε,ε∈Ioo 0 ε₀ → ‖F m ε-G ε‖≤A*(1+|Real.log ε|)*ρ^m)
    (hgradient : ∀ m ε,ε∈Ioo 0 ε₀ → ‖F' m ε-G' ε‖≤B*(1+|Real.log ε|)*ρ^m)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) : HasDerivAt G (G' ε) ε := by
  let a := ε/2
  let b := (ε+ε₀)/2
  have haε : a<ε := by dsimp [a]; linarith [hε.1]
  have hεb : ε<b := by dsimp [b]; linarith [hε.2]
  have hsub : Icc a b⊆Ioo 0 ε₀ := by
    intro x hx
    constructor <;> dsimp [a,b] at hx <;> linarith [hx.1,hx.2,hε.1,hε.2]
  have hlog : ContinuousOn Real.log (Icc a b) := fun x hx =>
    (Real.continuousAt_log (hsub hx).1.ne').continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hlog
  let M := 1+|C|
  have hM : 0≤M := by dsimp [M]; positivity
  have hlogbound (x : ℝ) (hx : x∈Ioo a b) : 1+|Real.log x|≤M := by
    have hh := (hC x ⟨hx.1.le,hx.2.le⟩).trans (le_abs_self C)
    dsimp [M]
    linarith [show |Real.log x|≤|C| by simpa only [Real.norm_eq_abs] using hh]
  have hp : Tendsto (fun m : ℕ => ρ^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have hv : TendstoUniformlyOn F G atTop (Ioo a b) := by
    apply preferred_uniform_limit_of_norm_bound F G (fun m => (A*M)*ρ^m)
    · simpa using hp.const_mul (A*M)
    · intro m x hx
      apply (hvalue m x (hsub ⟨hx.1.le,hx.2.le⟩)).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlogbound x hx) hA) (pow_nonneg hρ m)
  have hg : TendstoUniformlyOn F' G' atTop (Ioo a b) := by
    apply preferred_uniform_limit_of_norm_bound F' G' (fun m => (B*M)*ρ^m)
    · simpa using hp.const_mul (B*M)
    · intro m x hx
      apply (hgradient m x (hsub ⟨hx.1.le,hx.2.le⟩)).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlogbound x hx) hB) (pow_nonneg hρ m)
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hg
    (Filter.Eventually.of_forall (fun m x hx => hderiv m x (hsub ⟨hx.1.le,hx.2.le⟩)))
    (fun x hx => hv.tendsto_at hx) ⟨haε,hεb⟩

end
end IsingBulk.Preferred22
