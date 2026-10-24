import IsingBulk.Anisotropic.Geometry.AnalyticProfiles

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

theorem real_eq_inverse_or_neg_of_F1_zero {lam : ℝ} (hlam : 0<lam) {x y : ℝ}
    (hf : geometryF1 lam x y=0) :
    x=slicePInv lam (Real.cos y) ∨ x= -slicePInv lam (Real.cos y) := by
  rw [geometryF1_factor] at hf
  have he := (mul_eq_zero.mp hf).resolve_left (sq_pos_of_pos (Real.cosh_pos (lam*x))).ne'
  have hs : sliceP lam x^2=Real.cos y^2 := by linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · left
    rw [← h,sliceP_inv_apply hlam]
  · right
    have hn : Real.cos y=sliceP lam (-x) := by rw [sliceP_neg,h,neg_neg]
    rw [hn,sliceP_inv_apply hlam,neg_neg]

theorem edgeIntersectionProfile_zero_of_edges {lam : ℝ} (hlam : 0<lam) {x y : ℝ}
    (hf : geometryF1 lam x y=0) (hg : geometryF2 lam x y=0) : edgeIntersectionProfile lam y=0 := by
  rcases real_eq_inverse_or_neg_of_F1_zero hlam hf with h | h
  · simpa only [h,edgeIntersectionProfile] using hg
  · simpa [h,edgeIntersectionProfile,geometryF2,mul_neg,Real.cosh_neg,Real.sinh_neg] using hg

def edgeIntersectionSet (lam : ℝ) : Set ℂ :=
  {z | geometryF1 lam z.re z.im=0 ∧ geometryF2 lam z.re z.im=0}

/-- All edge intersections are locally finite, even at imaginary-axis contacts.
A globally analytic signed inverse avoids any rational-period endpoint argument. -/
theorem edgeIntersectionSet_locally_finite {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) (z : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ (edgeIntersectionSet lam ∩ U).Finite := by
  have hy := edgeIntersectionProfile_locally_nonzero hlam hne z.im
  rw [nhdsWithin,Filter.eventually_inf_principal] at hy
  have hreal : ∀ᶠ t in 𝓝 z.im, edgeIntersectionProfile lam t=0 → t=z.im := by
    filter_upwards [hy] with t ht he
    by_contra hn
    exact ht hn he
  have hw : ∀ᶠ w in 𝓝 z, w∈edgeIntersectionSet lam →
      w = (slicePInv lam (Real.cos z.im):ℂ)+(z.im:ℂ)*Complex.I ∨
      w = (-slicePInv lam (Real.cos z.im):ℂ)+(z.im:ℂ)*Complex.I := by
    filter_upwards [Complex.continuous_im.continuousAt.preimage_mem_nhds hreal] with w hw hE
    have him := hw (edgeIntersectionProfile_zero_of_edges hlam hE.1 hE.2)
    rcases real_eq_inverse_or_neg_of_F1_zero hlam hE.1 with hr | hr
    · left
      apply Complex.ext <;> simp [him,hr]
    · right
      apply Complex.ext <;> simp [him,hr]
  rcases mem_nhds_iff.mp hw with ⟨U,hUsub,hUopen,hzU⟩
  refine ⟨U,hUopen,hzU,?_⟩
  apply ((Set.finite_singleton ((-slicePInv lam (Real.cos z.im):ℂ)+(z.im:ℂ)*Complex.I)).insert
    ((slicePInv lam (Real.cos z.im):ℂ)+(z.im:ℂ)*Complex.I)).subset
  intro w hw
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hUsub hw.2 hw.1

end
end IsingBulk.Anisotropic
