import IsingBulk.Joint.RegularEdges.CompactLeadingAmplitude

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology

/-- A genuine uniform complex leading limit and a common nonzero amplitude
exclude cancellation uniformly; no positivity of the complex summands is used. -/
theorem uniform_leading_norm_lower {E A : Type*} {K : Set E} {l : Filter A}
    {F : A → E → ℂ} {g : E → ℂ} {c : ℝ} (hc : 0<c)
    (hg : ∀ e∈K, c≤‖g e‖) (hlim : TendstoUniformlyOn F g l K) :
    ∀ᶠ a in l, ∀ e∈K, c/2≤‖F a e‖ := by
  have h := Metric.tendstoUniformlyOn_iff.mp hlim (c/2) (half_pos hc)
  filter_upwards [h] with a ha
  intro e he
  have hd := ha e he
  have hn := norm_sub_norm_le (g e) (F a e)
  rw [← dist_eq_norm] at hn
  linarith [hg e he]

/-- The common scaled limit forces every member's actual unscaled derivative
to exceed any prescribed bound on one common punctured inward interval. -/
theorem uniform_scaled_leading_unbounded {E : Type*} {K : Set E}
    {F : ℝ → E → ℂ} {g : E → ℂ} {c : ℝ} (hc : 0<c)
    (hg : ∀ e∈K, c≤‖g e‖) {a : ℕ} (ha : 0<a)
    (hlim : TendstoUniformlyOn (fun (t : ℝ) e => ((t^a:ℝ):ℂ)*F t e) g (𝓝[>] (0:ℝ)) K) :
    ∀ M : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ e∈K, M<‖F t e‖ := by
  intro M
  have hb := uniform_leading_norm_lower hc hg hlim
  have ht : Tendsto (fun t : ℝ => t^a) (𝓝[>] 0) (𝓝 0) := by
    have ht' : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_pow (Nat.ne_of_gt ha)] using
      ht'.pow a
  have hp := ht.eventually (eventually_lt_nhds
    (div_pos (half_pos hc) (show 0<max M 0+1 by positivity)))
  filter_upwards [hb,hp,self_mem_nhdsWithin] with t hb hp htpos
  intro e he
  have hn := hb e he
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (pow_pos htpos a)] at hn
  by_contra hbad
  have hm : ‖F t e‖≤max M 0+1 := (le_of_not_gt hbad).trans (by linarith [le_max_left M 0])
  have hmul := mul_le_mul_of_nonneg_left hm (pow_nonneg htpos.le a)
  have hsmall : t^a*(max M 0+1)<c/2 := (lt_div_iff₀ (by positivity)).mp hp
  linarith

end
end IsingBulk.Joint.RegularEdges
