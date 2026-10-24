import IsingBulk.Anisotropic.NegativeCycles.WindingTranslation

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric
open scoped BigOperators

/-- Closed actual winding ellipsoids are compact, including empty sectors. -/
theorem isCompact_winding_energy_sublevel (n : ℕ) (k : Fin (n+2)) (σ : ℝ) :
    IsCompact {v : Fin n→ℝ | (∑i,(windingAffine n k v i)^2)≤σ} := by
  have hc : IsClosed {v : Fin n→ℝ | (∑i,(windingAffine n k v i)^2)≤σ} :=
    isClosed_le (windingAffine_energy_continuous n k) continuous_const
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin n→ℝ) (Real.sqrt (max σ 0))) hc
  intro v hv
  rw [mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  have hi := Finset.single_le_sum
    (fun j (_ : j∈(Finset.univ : Finset (Fin (n+1)))) => sq_nonneg (windingAffine n k v j))
    (Finset.mem_univ i.castSucc)
  have hi' : (v i)^2≤max σ 0 := by
    simpa only [windingAffine,Fin.snoc_castSucc] using hi.trans (hv.trans (le_max_left _ _))
  have hs := Real.sq_sqrt (le_max_right σ 0)
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (v i),Real.sqrt_nonneg (max σ 0),abs_nonneg (v i)]

end
end IsingBulk.Anisotropic.NegativeCycles
