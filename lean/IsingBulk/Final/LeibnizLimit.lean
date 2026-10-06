import IsingBulk.Final.LocalExtension

/-! The full finite Leibniz rule preserves the singular coefficient. Every
lower derivative limit is required; a top-derivative-only tail is insufficient. -/
namespace IsingBulk.Final
noncomputable section
open Filter
open scoped Topology BigOperators

theorem sqrt_radial_product_limit {f g : ℂ → ℂ} {z L : ℂ} (k : ℕ)
    (hg : AnalyticAt ℂ g z)
    (hf : ∀ᶠ e : ℝ in 𝓝[>] 0, ContDiffAt ℂ k f ((1+(e:ℂ))*z))
    (hlimits : ∀ i : ℕ, i ≤ k → Tendsto
      (fun e : ℝ => Real.sqrt e • iteratedDeriv i f ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (if i=k then L else 0))) :
    Tendsto (fun e : ℝ => Real.sqrt e • iteratedDeriv k (f*g) ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (L*g z)) := by
  have hp := radialPath_tendsto z
  have hgpath (i : ℕ) : Tendsto
      (fun e : ℝ => iteratedDeriv i g ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (iteratedDeriv i g z)) := by
    apply ContinuousAt.tendsto _ |>.comp hp
    simpa only [iteratedDeriv_eq_iterate] using (hg.iterated_deriv i).continuousAt
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k+1)) : Tendsto
      (fun e : ℝ => (k.choose i:ℂ) *
        (Real.sqrt e • iteratedDeriv i f ((1+(e:ℂ))*z)) *
        iteratedDeriv (k-i) g ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 ((k.choose i:ℂ)*(if i=k then L else 0)*iteratedDeriv (k-i) g z)) :=
    ((hlimits i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)).const_mul _).mul (hgpath _)
  have hsum := tendsto_finsetSum (Finset.range (k+1)) hterm
  have hval : (∑ i ∈ Finset.range (k+1),
      (k.choose i:ℂ)*(if i=k then L else 0)*iteratedDeriv (k-i) g z) = L*g z := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hik
      simp [hik]
    · simp
  rw [hval] at hsum
  apply hsum.congr'
  have hgan : ∀ᶠ e : ℝ in 𝓝[>] 0, AnalyticAt ℂ g ((1+(e:ℂ))*z) :=
    hp.eventually hg.eventually_analyticAt
  filter_upwards [hf,hgan] with e hfe hge
  rw [iteratedDeriv_mul hfe hge.contDiffAt, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.real_smul]
  ring

/-- Adding an analytic onsite/prefactor term contributes zero at this scale. -/
theorem sqrt_radial_add_analytic_limit {f b : ℂ → ℂ} {z L : ℂ} (k : ℕ)
    (hb : AnalyticAt ℂ b z)
    (hf : ∀ᶠ e : ℝ in 𝓝[>] 0, ContDiffAt ℂ k f ((1+(e:ℂ))*z))
    (hlim : Tendsto (fun e : ℝ => Real.sqrt e •
      iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun e : ℝ => Real.sqrt e •
      iteratedDeriv k (b+f) ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 L) := by
  have hp := radialPath_tendsto z
  have hbc : ContinuousAt (iteratedDeriv k b) z := by
    simpa only [iteratedDeriv_eq_iterate] using (hb.iterated_deriv k).continuousAt
  have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hbzero : Tendsto (fun e : ℝ => Real.sqrt e • iteratedDeriv k b ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa using hs.smul (hbc.tendsto.comp hp)
  have hsum := hbzero.add hlim
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hf,hp.eventually hb.eventually_analyticAt] with e hfe hbe
  rw [iteratedDeriv_add hbe.contDiffAt hfe, smul_add]

/-- Literal bulk prefactor composition: all derivative orders up to k enter.
This is a conditional analytic lemma; sector estimates are not assumptions of
an unconditional source natural-boundary theorem. -/
theorem sqrt_radial_bulk_limit {U m : ℂ → ℂ} {z L : ℂ} (k : ℕ)
    (hm : AnalyticAt ℂ m z)
    (hU : ∀ᶠ e : ℝ in 𝓝[>] 0, AnalyticAt ℂ U ((1+(e:ℂ))*z))
    (hlimits : ∀ i : ℕ, i ≤ k → Tendsto
      (fun e : ℝ => Real.sqrt e • iteratedDeriv i U ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (if i=k then 2*L else 0))) :
    Tendsto (fun e : ℝ => Real.sqrt e •
      iteratedDeriv k (fun s => 1-m s+2*m s*U s) ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (4*m z*L)) := by
  have hmul := sqrt_radial_product_limit (g := fun s => 2*m s) k
    (analyticAt_const.mul hm) (hU.mono (fun _ h => h.contDiffAt)) hlimits
  have hp := radialPath_tendsto z
  have hprod : ∀ᶠ e : ℝ in 𝓝[>] 0,
      ContDiffAt ℂ k (U*(fun s => 2*m s)) ((1+(e:ℂ))*z) := by
    filter_upwards [hU,hp.eventually hm.eventually_analyticAt] with e hUe hme
    exact (hUe.mul (analyticAt_const.mul hme)).contDiffAt
  have h := sqrt_radial_add_analytic_limit (b := fun s => 1-m s) k (analyticAt_const.sub hm) hprod hmul
  convert h using 1
  · funext e
    congr 2
    funext s
    simp only [Pi.add_apply,Pi.mul_apply]
    ring
  · congr 1
    ring

end
end IsingBulk.Final
