import IsingBulk.Tail.AllBranchExteriorShape

namespace IsingBulk.Tail
noncomputable section

theorem allBranchExterior_diameter_sub_bound {N : ℕ} (u v : Fin N → ℝ) :
    allBranchExteriorDiameter u ≤ allBranchExteriorDiameter v+2*‖u-v‖ := by
  by_cases hu : 0 < allBranchExteriorDiameter u
  · obtain ⟨p,q,_,hpq⟩ := allBranchExterior_diameter_attained u hu
    rw [← hpq]
    have hp := norm_le_pi_norm (u-v) p
    have hq := norm_le_pi_norm (u-v) q
    change ‖u p-v p‖ ≤ ‖u-v‖ at hp
    change ‖u q-v q‖ ≤ ‖u-v‖ at hq
    have he : u p-u q=(u p-v p)+(v p-v q)-(u q-v q) := by ring
    have hh := (norm_sub_le ((u p-v p)+(v p-v q)) (u q-v q)).trans
      (add_le_add (norm_add_le (u p-v p) (v p-v q)) (le_refl ‖u q-v q‖))
    rw [← he] at hh
    have hd := allBranchExterior_pair_le_diameter v p q
    simp only [Real.norm_eq_abs] at hh hp hq
    linarith
  · have hd := allBranchExterior_diameter_nonneg v
    have hn := norm_nonneg (u-v)
    linarith

theorem allBranchExterior_diameter_lipschitz {N : ℕ} :
    LipschitzWith 2 (@allBranchExteriorDiameter N) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  have hu := allBranchExterior_diameter_sub_bound u v
  have hv := allBranchExterior_diameter_sub_bound v u
  rw [norm_sub_rev] at hv
  simp only [NNReal.coe_ofNat,dist_eq_norm,Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith

theorem allBranchExterior_diameter_continuous {N : ℕ} :
    Continuous (@allBranchExteriorDiameter N) := allBranchExterior_diameter_lipschitz.continuous

theorem allBranchExterior_diameter_zero_iff {N : ℕ} (u : Fin N → ℝ) :
    allBranchExteriorDiameter u=0 ↔ ∀ p q, u p=u q := by
  constructor
  · intro hu p q
    have hh := allBranchExterior_pair_le_diameter u p q
    rw [hu] at hh
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  · intro hu
    by_contra hne
    have hp := lt_of_le_of_ne (allBranchExterior_diameter_nonneg u) (Ne.symm hne)
    obtain ⟨p,q,_,hh⟩ := allBranchExterior_diameter_attained u hp
    rw [hu p q,sub_self,abs_zero] at hh
    exact hne hh.symm

theorem allBranchExterior_equality_distance {N : ℕ} (u a : Fin N → ℝ)
    (ha : ∀ p q, a p=a q) : allBranchExteriorDiameter u ≤ 2*‖u-a‖ := by
  have hh := allBranchExterior_diameter_sub_bound u a
  rwa [(allBranchExterior_diameter_zero_iff a).mpr ha,zero_add] at hh

end
end IsingBulk.Tail
