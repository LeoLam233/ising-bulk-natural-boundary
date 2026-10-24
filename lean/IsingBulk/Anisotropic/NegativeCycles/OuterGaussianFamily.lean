import IsingBulk.Anisotropic.NegativeDominance.ParticleCauchyGaussian
import IsingBulk.Anisotropic.NegativeDominance.GaussianErrorSum

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Uniform Gaussian control of actual coefficient families from their proved
c/N Cauchy estimate. It includes every particle, and every selected subseries. -/
theorem outer_coefficient_family_gaussian {r C M δ K : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (hδ : 0<δ) :
    ∃a D L Q : ℝ,0<a ∧ 0<D ∧ 0<L ∧ 0<Q ∧
      ∀F : ℕ→ℕ→ℂ,
      (∀n j : ℕ,‖F n j‖≤K*particleEdgeMajorant r C M (n+1)*((n+1:ℕ)/δ)^j) →
      (∀n j : ℕ,‖F n j‖≤
        Real.exp (-a*(n+1:ℕ)^2+((j:ℝ)+1)*Real.log (n+1:ℕ)+L*((j:ℝ)+1))) ∧
      ∀j : ℕ,Summable (fun n=>F n j) ∧ Summable (fun n=>‖F n j‖) ∧
        (∑'n,‖F n j‖)≤D*Real.exp (((j:ℝ)+1)/2*Real.log ((j:ℝ)+2)+Q*((j:ℝ)+1)) ∧
        ∀E : Set ℕ,Summable (fun n=>if n∈E then F n j else 0) ∧
          ‖∑'n,if n∈E then F n j else 0‖≤
            D*Real.exp (((j:ℝ)+1)/2*Real.log ((j:ℝ)+2)+Q*((j:ℝ)+1)) := by
  classical
  let K' : ℝ := 1+|K|
  have hK' : 0<K' := by dsimp [K']; positivity
  have hKK' : K≤K' := by dsimp [K']; linarith [le_abs_self K]
  obtain ⟨a,L,ha,hL,hg⟩ := particle_cauchy_gaussian_bound hr hr1 hC hM hδ hK'
  obtain ⟨D,hD,hsum⟩ := gaussian_selected_norm_sum ha L (fun n : ℕ=>n+1) (by intro x y h; exact Nat.add_right_cancel h)
  refine ⟨a,D,L,L+|Real.log a|/2,ha,hD,hL,by positivity,?_⟩
  intro F hF
  have hb (n j : ℕ) : ‖F n j‖≤
      Real.exp (-a*(n+1:ℕ)^2+((j:ℝ)+1)*Real.log (n+1:ℕ)+L*((j:ℝ)+1)) := by
    apply (hF n j).trans
    apply le_trans _ (hg (n+1) (by omega) j)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK' (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (by positivity)
  refine ⟨hb,?_⟩
  intro j
  obtain ⟨hsF,hsnorm,hbound⟩ := hsum j (fun n=>F n j) (fun n=>hb n j)
  refine ⟨hsF,hsnorm,hbound,?_⟩
  intro E
  have hsel (n : ℕ) : ‖if n∈E then F n j else 0‖≤‖F n j‖ := by
    split
    · rfl
    · simpa only [norm_zero] using norm_nonneg (F n j)
  have hsn := hsnorm.of_nonneg_of_le (fun _=>norm_nonneg _) hsel
  refine ⟨hsn.of_norm,?_⟩
  exact (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hsel hsnorm).trans hbound)

theorem selected_particle_coefficient_family_gaussian {r C M δ K : ℝ}
    (idx : ℕ→ℕ) (hi : Function.Injective idx) (hidx : ∀ n : ℕ, 1 ≤ idx n)
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (hδ : 0<δ) :
    ∃a D L Q : ℝ,0<a ∧ 0<D ∧ 0<L ∧ 0<Q ∧
      ∀F : ℕ→ℕ→ℂ,
      (∀n j : ℕ,‖F n j‖≤K*particleEdgeMajorant r C M (idx n)*((idx n:ℕ)/δ)^j) →
      (∀n j : ℕ,‖F n j‖≤
        Real.exp (-a*(idx n:ℕ)^2+((j:ℝ)+1)*Real.log (idx n)+L*((j:ℝ)+1))) ∧
      ∀j : ℕ,Summable (fun n=>F n j) ∧ Summable (fun n=>‖F n j‖) ∧
        (∑'n,‖F n j‖)≤D*Real.exp (((j:ℝ)+1)/2*Real.log ((j:ℝ)+2)+Q*((j:ℝ)+1)) ∧
        ∀E : Set ℕ,Summable (fun n=>if n∈E then F n j else 0) ∧
          ‖∑'n,if n∈E then F n j else 0‖≤
            D*Real.exp (((j:ℝ)+1)/2*Real.log ((j:ℝ)+2)+Q*((j:ℝ)+1)) := by
  classical
  let K' : ℝ := 1+|K|
  have hK' : 0<K' := by dsimp [K']; positivity
  have hKK' : K≤K' := by dsimp [K']; linarith [le_abs_self K]
  obtain ⟨a,L,ha,hL,hg⟩ := particle_cauchy_gaussian_bound hr hr1 hC hM hδ hK'
  obtain ⟨D,hD,hsum⟩ := gaussian_selected_norm_sum ha L idx hi
  refine ⟨a,D,L,L+|Real.log a|/2,ha,hD,hL,by positivity,?_⟩
  intro F hF
  have hb (n j : ℕ) : ‖F n j‖≤
      Real.exp (-a*(idx n:ℕ)^2+((j:ℝ)+1)*Real.log (idx n)+L*((j:ℝ)+1)) := by
    apply (hF n j).trans
    apply le_trans _ (hg (idx n) (hidx n) j)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK' (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (by positivity)
  refine ⟨hb,?_⟩
  intro j
  obtain ⟨hsF,hsnorm,hbound⟩ := hsum j (fun n=>F n j) (fun n=>hb n j)
  refine ⟨hsF,hsnorm,hbound,?_⟩
  intro E
  have hsel (n : ℕ) : ‖if n∈E then F n j else 0‖≤‖F n j‖ := by
    split
    · rfl
    · simpa only [norm_zero] using norm_nonneg (F n j)
  have hsn := hsnorm.of_nonneg_of_le (fun _=>norm_nonneg _) hsel
  refine ⟨hsn.of_norm,?_⟩
  exact (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hsel hsnorm).trans hbound)

end IsingBulk.Anisotropic.NegativeCycles
