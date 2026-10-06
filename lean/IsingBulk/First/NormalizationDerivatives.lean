import IsingBulk.First.FormFactorAnalytic

/-! The exact all-order derivative normalization bridge. Local equalities are
established on a fixed-radius complex neighborhood before differentiating. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology

theorem standardFormFactor_iteratedDeriv_eq (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (standardFormFactor N r) s =
      iteratedDeriv j (onsiteFormFactor N r) s + 2*iteratedDeriv j (doubleFormFactor N r) s := by
  have hs := dampingDomain_of_margin hr hr1 hm
  have he : standardFormFactor N r =ᶠ[𝓝 s]
      (fun t => onsiteFormFactor N r t+2*doubleFormFactor N r t) := by
    filter_upwards [dampingDomain_mem_nhds hs] with t ht
    exact standardFormFactor_eq_onsite_add_double N hN r t (globalRoot t)
      (globalRoot_admissible hr hr1 ht.2)
  obtain ⟨hD,hO,_hS⟩ := formFactors_analyticAt N hN hr hr1 hm
  rw [he.iteratedDeriv_eq j]
  have h2 : AnalyticAt ℂ (fun t => 2*doubleFormFactor N r t) s := by
    convert! (analyticAt_const (v := (2:ℂ))).mul hD using 1
  rw [iteratedDeriv_fun_add hO.contDiffAt h2.contDiffAt, iteratedDeriv_const_mul_field]

theorem upperFormFactor_iteratedDeriv_normalization (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    2*iteratedDeriv j (upperFormFactor N) s =
      iteratedDeriv j (standardFormFactor N r) s-iteratedDeriv j (onsiteFormFactor N r) s := by
  rw [upperFormFactor_iteratedDeriv_fixed_radius N hN j hr hr1 hm,
    standardFormFactor_iteratedDeriv_eq N hN j hr hr1 hm]
  ring

/-- The source lower-order transfer only needs the published full-site bound
and the separate actual onsite estimate at the same permitted radius. -/
theorem upperFormFactor_iteratedDeriv_norm_bound (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    ‖iteratedDeriv j (upperFormFactor N) s‖ ≤
      (‖iteratedDeriv j (standardFormFactor N r) s‖+
        ‖iteratedDeriv j (onsiteFormFactor N r) s‖)/2 := by
  have he := upperFormFactor_iteratedDeriv_normalization N hN j hr hr1 hm
  have hn := norm_sub_le (iteratedDeriv j (standardFormFactor N r) s)
    (iteratedDeriv j (onsiteFormFactor N r) s)
  rw [← he, norm_mul, Complex.norm_ofNat] at hn
  linarith

end
end IsingBulk.First
