import IsingBulk.Anisotropic.NegativeDominance.GeometricDominance

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology BigOperators

theorem model_ne_zero_of_prefactor (B R H : ℂ) (s : ℝ) (n j : ℕ)
    (hn : 0<n) (hj : alpha n ≤ j) (hp : modelPrefactor B R H s n ≠ 0) :
    model B R H s n j ≠ 0 := by
  rw [model_factor_order]
  have ht : (tau n : ℂ) ≠ 0 := by exact_mod_cast (tau_pos n hn).ne'
  have hg : ((Real.Gamma ((j : ℝ)+1-alpha n)/Real.Gamma ((j : ℝ)+1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (model_gamma_pos n j hj).ne'
  exact mul_ne_zero (mul_ne_zero hp (zpow_ne_zero _ ht)) hg

/-- Sum over arbitrary finite sets covering the whole middle Gamma range.
For q=1 these are all odd particle indices in that range, not a fixed window.
The bound tends to zero relative to the selected main model. -/
theorem physical_model_middle_sum
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2 = B t) (hphi : Real.sin phi ≠ 0)
    (q : ℕ) (hq : 0 < q) :
    ∃ Nlow N : ℕ, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧ n ≤ j ∧
      physicalModel B rootB phi (n+2*q) j ≠ 0 ∧
      ∀ Sf Sb : Finset ℕ, 0 ∉ Sf → 0 ∉ Sb →
      (∀ k ∈ Sf, 2*alpha (n+2*q+2*q*k) ≤ j) →
      (∀ k ∈ Sb, 2*q*k ≤ n+2*q ∧ Nlow ≤ n+2*q-2*q*k) →
      (∑ k ∈ Sf, ‖physicalModel B rootB phi (n+2*q+2*q*k) j‖)+
      (∑ k ∈ Sb, ‖physicalModel B rootB phi (n+2*q-2*q*k) j‖) ≤
        2*‖physicalModel B rootB phi (n+2*q) j‖*
          (Real.exp (-((q : ℝ)^2/2*Real.log j))/
            (1-Real.exp (-((q : ℝ)^2/2*Real.log j)))) := by
  obtain ⟨Nlow, Ns, hs⟩ := physical_model_middle_dominance B rootB phi hB hB0 hroot hroot0 hsq hphi q hq
  obtain ⟨Np, hp⟩ := eventually_atTop.mp (physical_prefactor_eventually_nonzero B rootB phi hB hB0 hroot hroot0 hphi)
  refine ⟨Nlow, max Ns (max Np 2), ?_⟩
  intro n hn ho
  have hnNs : Ns≤n := (le_max_left _ _).trans hn
  have hnNp : Np≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : 2≤n := by omega
  obtain ⟨j, hjL, hjH, hnj, hAj, hf, hb⟩ := hs n hnNs ho
  have htj : alpha (n+2*q) ≤ j :=
    (alpha_mono (by omega : n+2*q≤n+4*q)).trans (by omega)
  have hw : physicalModel B rootB phi (n+2*q) j ≠ 0 :=
    model_ne_zero_of_prefactor _ _ _ _ _ _ (by omega) htj (hp _ (by omega))
  refine ⟨j, hjL, hjH, hnj, hw, ?_⟩
  intro Sf Sb hSf hSb hSfA hSbA
  let a : ℝ := (q : ℝ)^2/2*Real.log j
  have ha : 0<a := by
    have hqR : 0<(q : ℝ) := by exact_mod_cast hq
    have hjR : 1<(j : ℝ) := by exact_mod_cast (show 1<j by omega)
    exact mul_pos (div_pos (sq_pos_of_pos hqR) (by norm_num)) (Real.log_pos hjR)
  have hsf := finite_norm_sum_of_log_gaps
    (fun k => physicalModel B rootB phi (n+2*q+2*q*k) j) _ hw a ha Sf hSf
    (fun k hk => hf k (hSfA k hk))
  have hsb := finite_norm_sum_of_log_gaps
    (fun k => physicalModel B rootB phi (n+2*q-2*q*k) j) _ hw a ha Sb hSb
    (fun k hk => hb k (hSbA k hk).1 (hSbA k hk).2)
  dsimp [a] at hsf hsb
  linarith only [hsf, hsb]

end
end IsingBulk.Anisotropic.NegativeDominance
