import IsingBulk.Anisotropic.Algebra.PairedEnumeration

namespace IsingBulk.Anisotropic.Algebra
noncomputable section

theorem nodup_of_pairProduct_ne_zero (xs : List ℂ)
    (h : IsingBulk.Schur.pairProduct schurKernel xs ≠ 0) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [IsingBulk.Schur.pairProduct, mul_ne_zero_iff] at h
    refine List.nodup_cons.mpr ⟨?_,ih h.2⟩
    intro ha
    have hm : (0:ℂ) ∈ xs.map (schurKernel a) :=
      List.mem_map.mpr ⟨a,ha,schurKernel_self a⟩
    exact h.1 (List.prod_eq_zero hm)

theorem pairedList_nodup_iff {n : ℕ} (v : PairIndex n → ℂ) :
    (pairedList v).Nodup ↔ Function.Injective v := by
  rw [pairedList_eq_map,List.nodup_map_iff_inj_on (nodup_pairedIndices n)]
  constructor
  · intro h i j he
    exact h i (mem_pairedIndices i) j (mem_pairedIndices j) he
  · intro h i _ j _ he
    exact h he

/-- Full Schur determinant identity, including all coincident coordinates. -/
theorem even_schur_det {n : ℕ} (v : PairIndex n → ℂ)
    (hd : ∀ i j, 1-v i*v j ≠ 0) :
    (schurMatrix v).det = (IsingBulk.Schur.pairProduct schurKernel (pairedList v))^2 := by
  by_cases hi : Function.Injective v
  · exact even_schur_det_of_injective v hi hd
  · have hp : IsingBulk.Schur.pairProduct schurKernel (pairedList v) = 0 := by
      by_contra hn
      exact hi ((pairedList_nodup_iff v).mp (nodup_of_pairProduct_ne_zero _ hn))
    obtain ⟨i,j,hv,hij⟩ := Function.not_injective_iff.mp hi
    have hm : (schurMatrix v).det = 0 := Matrix.det_zero_of_row_eq hij (by
      funext k
      simp only [schurMatrix,hv])
    simp [hm,hp]

end
end IsingBulk.Anisotropic.Algebra
