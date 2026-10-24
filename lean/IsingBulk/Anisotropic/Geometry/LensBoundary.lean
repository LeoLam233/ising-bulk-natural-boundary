import IsingBulk.Anisotropic.Geometry.Components

namespace IsingBulk.Anisotropic
noncomputable section

theorem central_strip_bounds_le {lam y : ℝ} (hlam : 0<lam) (hy : |y|≤sliceY lam) :
    |y|≤Real.pi/2 ∧ |lam*y|≤Real.pi/2 := by
  have hm : 0<max 1 lam := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hm)).mp hy
  have h1 := le_max_left (1:ℝ) lam
  have h2 := le_max_right (1:ℝ) lam
  rw [abs_mul,abs_of_pos hlam]
  constructor <;> nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr h1),
    mul_nonneg (abs_nonneg y) (sub_nonneg.mpr h2)]

theorem sliceH_nonneg_closed_strip {lam y : ℝ} (hlam : 0<lam) (hy : |y|≤sliceY lam) :
    0≤sliceH lam y := by
  have hb := central_strip_bounds_le hlam hy
  apply le_min
  · have hc := Real.cos_nonneg_of_mem_Icc (abs_le.mp hb.1)
    simpa only [slicePInv_zero hlam] using (slicePInv_strictMono hlam).monotone hc
  · have hc := Real.cos_nonneg_of_mem_Icc (abs_le.mp hb.2)
    simpa only [sliceQInv_zero hlam] using (sliceQInv_strictMono hlam).monotone hc

theorem sliceH_zero_at_endpoint {lam y : ℝ} (hlam : 0<lam) (hy : |y|=sliceY lam) :
    sliceH lam y=0 := by
  apply le_antisymm _ (sliceH_nonneg_closed_strip hlam hy.le)
  rcases strip_endpoint_cos_zero hlam hy with h | h
  · unfold sliceH
    exact (min_le_left _ _).trans_eq (by rw [h,slicePInv_zero hlam])
  · unfold sliceH
    exact (min_le_right _ _).trans_eq (by rw [h,sliceQInv_zero hlam])

theorem closure_omegaH_profile_bounds {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈closure (omegaH lam)) :
    |z.im|≤sliceY lam ∧ |z.re|≤sliceH lam z.im := by
  refine ⟨(closure_omegaH_bounds hlam hz).1,?_⟩
  have h : closure (omegaH lam) ⊆ {z : ℂ | |z.re|≤sliceH lam z.im} := by
    apply closure_minimal
    · intro w hw
      exact hw.2.le
    · exact isClosed_le Complex.continuous_re.abs ((sliceH_continuous hlam).comp Complex.continuous_im)
  exact h hz

def highBoundaryPoint (lam e y : ℝ) : ℂ := (e*sliceH lam y:ℝ)+(y:ℂ)*Complex.I

theorem highBoundaryPoint_continuous {lam : ℝ} (hlam : 0<lam) (e : ℝ) :
    Continuous (highBoundaryPoint lam e) := by
  unfold highBoundaryPoint
  exact (Complex.continuous_ofReal.comp (continuous_const.mul (sliceH_continuous hlam))).add
    (Complex.continuous_ofReal.mul continuous_const)

theorem highBoundaryPoint_mem_frontier_open {lam e y : ℝ} (hlam : 0<lam) (he : |e|=1)
    (hy : |y|<sliceY lam) : highBoundaryPoint lam e y∈frontier (omegaH lam) := by
  let x := e*sliceH lam y
  have hx : |x|=sliceH lam y := by simp only [x,abs_mul,he,one_mul,abs_of_pos (sliceH_pos hlam hy)]
  let g : ℝ→ℂ := fun t => ((t*x:ℝ):ℂ)+(y:ℂ)*Complex.I
  have hg : Continuous g := by fun_prop
  have hm : Set.MapsTo g (Set.Ioo (0:ℝ) 1) (omegaH lam) := by
    intro t ht
    constructor
    · simpa [g] using hy
    · simp only [g,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        sub_zero,add_zero,zero_add]
      rw [abs_mul,abs_of_pos ht.1,hx]
      nlinarith [sliceH_pos hlam hy,ht.2]
  have hcl : (1:ℝ)∈closure (Set.Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
    exact ⟨by norm_num,le_rfl⟩
  rw [(omegaH_isOpen hlam).frontier_eq]
  refine ⟨?_,?_⟩
  · simpa only [g,one_mul,x,highBoundaryPoint] using hm.closure hg hcl
  · intro h
    have hi := h.2
    change |(highBoundaryPoint lam e y).re|<sliceH lam (highBoundaryPoint lam e y).im at hi
    simp [highBoundaryPoint,abs_mul,he,abs_of_pos (sliceH_pos hlam hy)] at hi

theorem highBoundaryPoint_mem_frontier {lam e y : ℝ} (hlam : 0<lam) (he : |e|=1)
    (hy : |y|≤sliceY lam) : highBoundaryPoint lam e y∈frontier (omegaH lam) := by
  have hm : Set.MapsTo (highBoundaryPoint lam e) (Set.Ioo (-sliceY lam) (sliceY lam))
      (frontier (omegaH lam)) := fun _ ht => highBoundaryPoint_mem_frontier_open hlam he (abs_lt.mpr ht)
  have hcl : y∈closure (Set.Ioo (-sliceY lam) (sliceY lam)) := by
    rw [closure_Ioo (by linarith [sliceY_pos hlam] : -sliceY lam≠sliceY lam)]
    exact abs_le.mp hy
  have h := hm.closure (highBoundaryPoint_continuous hlam e) hcl
  rwa [isClosed_frontier.closure_eq] at h

/-- The complete lens boundary, including its two tips. -/
theorem mem_frontier_omegaH_iff {lam : ℝ} (hlam : 0<lam) (z : ℂ) :
    z∈frontier (omegaH lam) ↔ |z.im|≤sliceY lam ∧ |z.re|=sliceH lam z.im := by
  constructor
  · intro hz
    have hb := closure_omegaH_profile_bounds hlam (frontier_subset_closure hz)
    refine ⟨hb.1,le_antisymm hb.2 ?_⟩
    by_cases hy : |z.im|<sliceY lam
    · rw [(omegaH_isOpen hlam).frontier_eq] at hz
      exact le_of_not_gt (fun h => hz.2 ⟨hy,h⟩)
    · rw [sliceH_zero_at_endpoint hlam (le_antisymm hb.1 (le_of_not_gt hy))]
      exact abs_nonneg _
  · rintro ⟨hy,hx⟩
    by_cases hr : 0≤z.re
    · have he : z=highBoundaryPoint lam 1 z.im := by
        apply Complex.ext
        · simpa [highBoundaryPoint,abs_of_nonneg hr] using hx
        · simp [highBoundaryPoint]
      rw [he]
      exact highBoundaryPoint_mem_frontier hlam (by norm_num) hy
    · have he : z=highBoundaryPoint lam (-1) z.im := by
        apply Complex.ext
        · simp only [highBoundaryPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
            Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,neg_mul,one_mul]
          rw [abs_of_neg (lt_of_not_ge hr)] at hx
          linarith
        · simp [highBoundaryPoint]
      rw [he]
      exact highBoundaryPoint_mem_frontier hlam (by norm_num) hy

end
end IsingBulk.Anisotropic
