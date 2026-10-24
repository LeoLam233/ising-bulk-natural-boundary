import IsingBulk.Anisotropic.NegativeDominance.AngularRootQuadratic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (z w : ι→ℂ)
    (hz : ∀i∈s,‖z i‖≤1) (hw : ∀i∈s,‖w i‖≤1) :
    ‖(∏i∈s,z i)-(∏i∈s,w i)‖≤∑i∈s,‖z i-w i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs := ih (fun i hi=>hz i (Finset.mem_insert_of_mem hi)) (fun i hi=>hw i (Finset.mem_insert_of_mem hi))
    have hwp : ‖∏i∈s,w i‖≤1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i hi=>hw i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    calc
      _ = ‖z a*((∏i∈s,z i)-(∏i∈s,w i))+(z a-w a)*(∏i∈s,w i)‖ := by congr 1; ring
      _ ≤ ‖z a‖*‖(∏i∈s,z i)-(∏i∈s,w i)‖+‖z a-w a‖*‖∏i∈s,w i‖ := by
        simpa only [norm_mul] using norm_add_le
          (z a*((∏i∈s,z i)-(∏i∈s,w i))) ((z a-w a)*(∏i∈s,w i))
      _ ≤ 1*(∑i∈s,‖z i-w i‖)+‖z a-w a‖*1 :=
        add_le_add (mul_le_mul (hz a (Finset.mem_insert_self _ _)) hs (norm_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hwp (norm_nonneg _))
      _ = _ := by ring

/-- The total angular phase error is controlled by the full quadratic sum,
without an extraneous factor of the particle number. -/
theorem edgeRoot_product_angular_variation {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im) :
    ∃K : ℝ,0<K ∧ ∀N : ℕ,∀q : Fin N→ℝ,
      ‖(∏i,edgeRoot b B (q i))-continuedRoot (b : ℂ)^N‖≤K*∑i,(q i)^2 := by
  obtain ⟨K,hK,hq⟩ := edgeRoot_angular_quadratic hb hB
  refine ⟨K,hK,?_⟩
  intro N q
  have hbase : ‖continuedRoot (b : ℂ)‖≤1 := by
    simpa [edgeRoot,edgeW] using (edgeRoot_bounds hb hB 0).1
  have hh := norm_prod_sub_prod_le_sum Finset.univ (fun i=>edgeRoot b B (q i)) (fun _=>continuedRoot (b : ℂ))
    (fun i _=>(edgeRoot_bounds hb hB (q i)).1) (fun _ _=>hbase)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  exact hh.trans (by rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _=>hq (q i)))

end
end IsingBulk.Anisotropic.NegativeDominance
