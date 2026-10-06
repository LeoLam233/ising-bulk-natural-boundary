import IsingBulk.Tail.CompactPairWeightJets
import IsingBulk.Tail.AllBranchExteriorEqualityGeometry

namespace IsingBulk.Tail
noncomputable section

/-- Diameter over a fixed allowed set of pairs, including deleted-coordinate sets. -/
def compactAllowedDiameter {N : ℕ} (P : Finset (Fin N × Fin N)) (θ : Fin N → ℝ) : ℝ :=
  (P.sup (fun p => ‖θ p.1-θ p.2‖₊) : NNReal)

theorem compactAllowedDiameter_nonneg {N : ℕ} (P : Finset (Fin N × Fin N)) (θ : Fin N → ℝ) :
    0 ≤ compactAllowedDiameter P θ := NNReal.coe_nonneg _

theorem compactAllowedDiameter_pair_le {N : ℕ} (P : Finset (Fin N × Fin N))
    (θ : Fin N → ℝ) {p : Fin N × Fin N} (hp : p ∈ P) :
    |θ p.1-θ p.2| ≤ compactAllowedDiameter P θ := by
  have h := NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun q => ‖θ q.1-θ q.2‖₊) hp)
  simpa only [compactAllowedDiameter,coe_nnnorm,Real.norm_eq_abs] using h

theorem compactAllowedDiameter_attained {N : ℕ} (P : Finset (Fin N × Fin N))
    (θ : Fin N → ℝ) (hθ : 0 < compactAllowedDiameter P θ) :
    ∃ p ∈ P, |θ p.1-θ p.2|=compactAllowedDiameter P θ := by
  have hpos : (0:NNReal) < P.sup (fun p => ‖θ p.1-θ p.2‖₊) := hθ
  obtain ⟨p,hp,hle⟩ := (Finset.le_sup_iff hpos).mp (le_refl (P.sup (fun p => ‖θ p.1-θ p.2‖₊)))
  refine ⟨p,hp,le_antisymm (compactAllowedDiameter_pair_le P θ hp) ?_⟩
  exact_mod_cast hle

theorem compactAllowedDiameter_le_full {N : ℕ} (P : Finset (Fin N × Fin N))
    (θ : Fin N → ℝ) : compactAllowedDiameter P θ ≤ allBranchExteriorDiameter θ := by
  by_cases hθ : 0 < compactAllowedDiameter P θ
  · obtain ⟨p,_,he⟩ := compactAllowedDiameter_attained P θ hθ
    rw [← he]
    exact allBranchExterior_pair_le_diameter θ p.1 p.2
  · exact (le_of_not_gt hθ).trans (allBranchExterior_diameter_nonneg θ)

theorem compactAllowedDiameter_sub_bound {N : ℕ} (P : Finset (Fin N × Fin N))
    (u v : Fin N → ℝ) : compactAllowedDiameter P u ≤ compactAllowedDiameter P v+2*‖u-v‖ := by
  by_cases hu : 0 < compactAllowedDiameter P u
  · obtain ⟨⟨p,q⟩,hpq,he⟩ := compactAllowedDiameter_attained P u hu
    rw [← he]
    have hp := norm_le_pi_norm (u-v) p
    have hq := norm_le_pi_norm (u-v) q
    change ‖u p-v p‖ ≤ ‖u-v‖ at hp
    change ‖u q-v q‖ ≤ ‖u-v‖ at hq
    have heq : u p-u q=(u p-v p)+(v p-v q)-(u q-v q) := by ring
    have hh := (norm_sub_le ((u p-v p)+(v p-v q)) (u q-v q)).trans
      (add_le_add (norm_add_le (u p-v p) (v p-v q)) (le_refl ‖u q-v q‖))
    rw [← heq] at hh
    have hd := compactAllowedDiameter_pair_le P v hpq
    simp only [Real.norm_eq_abs] at hh hp hq
    linarith
  · have hd := compactAllowedDiameter_nonneg P v
    have hn := norm_nonneg (u-v)
    linarith

theorem compactAllowedDiameter_lipschitz {N : ℕ} (P : Finset (Fin N × Fin N)) :
    LipschitzWith 2 (compactAllowedDiameter P) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  have hu := compactAllowedDiameter_sub_bound P u v
  have hv := compactAllowedDiameter_sub_bound P v u
  rw [norm_sub_rev] at hv
  simp only [NNReal.coe_ofNat,dist_eq_norm,Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith

theorem compactAllowedDiameter_continuous {N : ℕ} (P : Finset (Fin N × Fin N)) :
    Continuous (compactAllowedDiameter P) := (compactAllowedDiameter_lipschitz P).continuous

theorem compactAllowedDiameter_denominator_pos {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (θ : Fin N → ℝ) (hθ : 0 < compactAllowedDiameter P θ) :
    0 < compactPairWeightDenom P M θ :=
  (pow_pos hθ _).trans_le (compactPairWeightDenom_lower P M θ _ (compactAllowedDiameter_attained P θ hθ))

end
end IsingBulk.Tail
