import IsingBulk.Anisotropic.NegativeCycles.ScalarPhaseGrowth

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric NegativeNormalForm
open scoped BigOperators

theorem exists_inner_phase_disk (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0)
    (r₀ ρ : ℝ) (hr₀ : 0<r₀) (hρ : 0<ρ) :
    ∃ c σ : ℝ, 0<c ∧ 0<σ ∧ c≤r₀/2 ∧
      ∀ n : ℕ, n≠0 → ∀ (t : ℂ) (v : Config n),
        ‖t‖<c/(n:ℝ) → absoluteEnergy v<σ →
        ‖t‖<r₀ ∧ ‖v‖<r₀ ∧ ‖poleEquation B phi hphi 0 t v‖<ρ := by
  obtain ⟨r,C,hr,hC,hgrowth⟩ := negativePhase_uniform_growth B phi hphi hB
  let a := min r r₀
  have ha : 0<a := lt_min hr hr₀
  let c := min (a/2) (ρ/(4*C))
  let σ := min ((a/2)^2) (ρ/(4*C))
  have hc : 0<c := lt_min (by positivity) (by positivity)
  have hσ : 0<σ := lt_min (sq_pos_of_pos (by positivity)) (by positivity)
  have hca : c≤a/2 := min_le_left _ _
  have hcρ : C*c≤ρ/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*C)).mp (min_le_right (a/2) (ρ/(4*C)))
    change c*(4*C)≤ρ at hh
    nlinarith
  have hσa : σ≤(a/2)^2 := min_le_left _ _
  have hσρ : C*σ≤ρ/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*C)).mp (min_le_right ((a/2)^2) (ρ/(4*C)))
    change σ*(4*C)≤ρ at hh
    nlinarith
  have har : a≤r := min_le_left _ _
  have har₀ : a≤r₀ := min_le_right _ _
  refine ⟨c,σ,hc,hσ,by linarith,?_⟩
  intro n hn t v ht hv
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have htc : ‖t‖<c := ht.trans_le (div_le_self hc.le hn1)
  have hnt : (n:ℝ)*‖t‖<c := by
    have hh := (lt_div_iff₀ hnpos).mp ht
    nlinarith
  have hvi (i : Fin n) : ‖v i‖≤a/2 := by
    have hi : ‖v i‖^2≤absoluteEnergy v :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have hvnorm : ‖v‖≤a/2 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr hvi
  have htr : ‖t‖<r := by linarith
  have hvr (i : Fin n) : ‖v i‖<r := by linarith [hvi i]
  have hphase := poleEquation_uniform_growth B phi hphi r C hgrowth t v htr hvr
  refine ⟨by linarith,by linarith,?_⟩
  have hterm1 : (n:ℝ)*C*‖t‖≤ρ/4 := by nlinarith
  have hterm2 : C*absoluteEnergy v≤ρ/4 := by nlinarith
  linarith

end
end IsingBulk.Anisotropic.NegativeCycles
