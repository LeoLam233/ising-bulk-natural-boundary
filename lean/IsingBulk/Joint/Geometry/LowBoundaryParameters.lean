import IsingBulk.Joint.Geometry.LowFaceParameter

namespace IsingBulk.Joint
noncomputable section
open Set

theorem realProduct_le_one_of_frontier_low {K : Coupling} (hK : K ∈ frontier lowDomain) :
    realProduct (K.1.re,K.2.re) ≤ 1 := by
  obtain ⟨hx,hu,_,_⟩ := closure_low_bounds (frontier_subset_closure hK)
  by_contra hn
  have hp : 1 < Real.sinh K.1.re*Real.sinh K.2.re := by
    simpa [realProduct,abs_of_nonneg hx,abs_of_nonneg hu] using lt_of_not_ge hn
  have hx' : 0 < K.1.re := by
    by_contra h
    have he : K.1.re = 0 := le_antisymm (le_of_not_gt h) hx
    norm_num [he] at hp
  have hu' : 0 < K.2.re := by
    by_contra h
    have he : K.2.re = 0 := le_antisymm (le_of_not_gt h) hu
    norm_num [he] at hp
  have h₁ := (real_edge_low_iff hx hu).mpr hp
  have h₂ := (real_edge_low_iff hu hx).mpr (by simpa [mul_comm] using hp)
  have hm : K ∈ lowDomain := ⟨hx',hu', (Real.abs_cos_le_one _).trans_lt h₁,
    (Real.abs_cos_le_one _).trans_lt h₂⟩
  exact (lowDomain_isOpen.frontier_eq ▸ hK).2 hm

theorem low_boundary_active_face {K : Coupling} (hK : K ∈ frontier lowDomain) :
    faceRatio1 (K.1.re,K.2.re) = |Real.cos K.1.im| ∨
    faceRatio2 (K.1.re,K.2.re) = |Real.cos K.2.im| := by
  obtain ⟨hx,hu,_,_⟩ := closure_low_bounds (frontier_subset_closure hK)
  obtain ⟨h₁,h₂⟩ := closure_low_inequalities (frontier_subset_closure hK)
  by_contra hn
  push Not at hn
  have he₁ : faceRatio1 (K.1.re,K.2.re) = Real.cosh K.1.re*Real.tanh K.2.re := by
    simp [faceRatio1,abs_of_nonneg hu]
  have he₂ : faceRatio2 (K.1.re,K.2.re) = Real.cosh K.2.re*Real.tanh K.1.re := by
    simp [faceRatio2,abs_of_nonneg hx]
  have hg₁ : |Real.cos K.1.im| < Real.cosh K.1.re*Real.tanh K.2.re := by
    exact lt_of_le_of_ne h₁ (by simpa only [he₁,ne_eq,eq_comm] using hn.1)
  have hg₂ : |Real.cos K.2.im| < Real.cosh K.2.re*Real.tanh K.1.re := by
    exact lt_of_le_of_ne h₂ (by simpa only [he₂,ne_eq,eq_comm] using hn.2)
  have hx' : 0 < K.1.re := by
    by_contra h
    have he : K.1.re = 0 := le_antisymm (le_of_not_gt h) hx
    have hh : |Real.cos K.2.im| < 0 := by simpa [he] using hg₂
    exact (not_lt_of_ge (abs_nonneg _)) hh
  have hu' : 0 < K.2.re := by
    by_contra h
    have he : K.2.re = 0 := le_antisymm (le_of_not_gt h) hu
    have hh : |Real.cos K.1.im| < 0 := by simpa [he] using hg₁
    exact (not_lt_of_ge (abs_nonneg _)) hh
  exact (lowDomain_isOpen.frontier_eq ▸ hK).2 ⟨hx',hu',hg₁,hg₂⟩

private theorem faceRatios_closed_bounds {v : ℝ × ℝ} (hp : realProduct v ≤ 1) :
    0 ≤ faceRatio1 v ∧ faceRatio1 v ≤ 1 ∧ 0 ≤ faceRatio2 v ∧ faceRatio2 v ≤ 1 := by
  have hn (x u : ℝ) : 0 ≤ Real.cosh x*Real.tanh |u| := by
    have ht : 0 ≤ Real.tanh |u| := by simpa using IsingBulk.Anisotropic.tanh_strictMono.monotone (abs_nonneg u)
    exact mul_nonneg (Real.cosh_pos _).le ht
  have h₁ : faceRatio1 v ≤ 1 := by
    by_contra h
    have hh := (real_edge_low_iff (abs_nonneg v.1) (abs_nonneg v.2)).mp
      (show 1 < Real.cosh |v.1| * Real.tanh |v.2| by simpa [cosh_abs_eq,faceRatio1] using lt_of_not_ge h)
    exact (not_lt_of_ge hp) hh
  have h₂ : faceRatio2 v ≤ 1 := by
    by_contra h
    have hh := (real_edge_low_iff (abs_nonneg v.2) (abs_nonneg v.1)).mp
      (show 1 < Real.cosh |v.2| * Real.tanh |v.1| by simpa [cosh_abs_eq,faceRatio2] using lt_of_not_ge h)
    exact (not_lt_of_ge hp) (by simpa [realProduct,mul_comm] using hh)
  exact ⟨hn _ _,h₁,hn _ _,h₂⟩

theorem low_first_face_parameter_exists {K : Coupling} (hK : K ∈ frontier lowDomain)
    (hface : faceRatio1 (K.1.re,K.2.re) = |Real.cos K.1.im|) :
    ∃ k l : ℤ, ∃ sgn τ a : ℝ, (sgn = -1 ∨ sgn = 1) ∧ (τ = -1 ∨ τ = 1) ∧
      |a| ≤ 1 ∧ lowFaceParameter k l sgn τ ((K.1.re,K.2.re),a) = K := by
  obtain ⟨hx,hu,_,_⟩ := closure_low_bounds (frontier_subset_closure hK)
  have hfree := (closure_low_inequalities (frontier_subset_closure hK)).2
  obtain ⟨_,_,hr₂,hr₂1⟩ := faceRatios_closed_bounds (realProduct_le_one_of_frontier_low hK)
  obtain ⟨k,sgn,hs,he₁⟩ := abs_cos_chart_representation hface.symm
  obtain ⟨l,τ,a,hτ,ha,he₂⟩ := cosine_free_chart_representation hr₂ hr₂1
    (show |Real.cos K.2.im| ≤ faceRatio2 (K.1.re,K.2.re) by
      simpa [faceRatio2,abs_of_nonneg hx] using hfree)
  refine ⟨k,l,sgn,τ,a,hs,hτ,ha,?_⟩
  apply Prod.ext <;> apply Complex.ext <;> simp [lowFaceParameter,←he₁,←he₂]

end
end IsingBulk.Joint
