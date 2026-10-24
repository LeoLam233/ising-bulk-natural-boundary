import IsingBulk.Anisotropic.RegularEdges.EdgeNeighborhood
import IsingBulk.HT.Contour.PhysicalAngularRegularity

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem odd_zero_momentum_not_all_pi {N : ℕ} (hN : Odd N) (q : Fin N → ℝ)
    (hq : ∑ i, q i=0) : ¬∀ i, Real.cos (q i)= -1 := by
  intro hall
  have hex (i : Fin N) : Complex.exp ((q i : ℂ)*Complex.I)= -1 := by
    have hs := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr (hall i))
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hall i, hs]
    norm_num
  have hp : (∏ i, Complex.exp ((q i : ℂ)*Complex.I))=1 := by
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, hq]
    simp
  simp only [hex, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hN.neg_one_pow] at hp
  norm_num at hp

theorem physicalDependentAngles_sum_zero (n : ℕ) (q : Fin n → ℝ) :
    ∑ i, physicalDependentAngles n q i=0 := by
  rw [Fin.sum_univ_castSucc]
  simp [physicalDependentAngles]

theorem edgeRoot_norm_one_implies_cos_one {b : ℝ} {B : ℂ}
    (hB : 0<B.im) (q : ℝ) (hn : ‖edgeRoot b B q‖=1) : Real.cos q=1 := by
  by_contra hq
  have hi : 0<(edgeW b B q).im := by
    rw [edgeW_im]
    exact mul_pos hB (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one q) hq))
  have hlt := interiorRoot_norm_lt_one hi
  rw [edgeRoot, continuedRoot_eq_interiorRoot hi] at hn
  linarith

/-- The actual odd zero-momentum torus excludes a full negative-edge collision,
so its lattice-root product has strictly subunit modulus at every point. -/
theorem odd_negative_root_product_lt_one {N : ℕ} (hN : Odd N)
    {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im)
    (q : Fin N → ℝ) (hq : ∑ i, q i=0) :
    ‖∏ i, edgeRoot b B (q i-Real.pi)‖<1 := by
  have hr (i : Fin N) : ‖edgeRoot b B (q i-Real.pi)‖≤1 := (edgeRoot_bounds hb hB _).1
  have hle : ‖∏ i, edgeRoot b B (q i-Real.pi)‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hr i)
  apply lt_of_le_of_ne hle
  intro he
  have hrN : ∀ i∈(Finset.univ : Finset (Fin N)), ‖edgeRoot b B (q i-Real.pi)‖₊≤1 := by
    intro i _
    exact_mod_cast hr i
  have heN : (∏ i, ‖edgeRoot b B (q i-Real.pi)‖₊)=1 := by
    apply NNReal.eq
    simpa only [NNReal.coe_prod, coe_nnnorm, NNReal.coe_one, ← norm_prod] using he
  have hi := (Finset.prod_eq_one_iff_of_le_one hrN).mp heN
  apply odd_zero_momentum_not_all_pi hN q hq
  intro i
  have hn := congrArg (fun x : NNReal => (x : ℝ)) (hi i (Finset.mem_univ i))
  have hc := edgeRoot_norm_one_implies_cos_one hB (q i-Real.pi) hn
  rw [Real.cos_sub_pi] at hc
  exact neg_eq_iff_eq_neg.mp hc

end
end IsingBulk.Anisotropic.NegativeDominance
