import IsingBulk.Anisotropic.Geometry.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Arsinh

namespace IsingBulk.Anisotropic
noncomputable section

theorem sliceP_continuous (lam : ℝ) : Continuous (sliceP lam) := by
  exact continuous_iff_continuousAt.mpr (fun x => (sliceP_hasDerivAt lam x).continuousAt)

theorem sliceP_unbounded {lam : ℝ} (hlam : 0 < lam) (y : ℝ) : ∃ x, y ≤ sliceP lam x := by
  have ht : 0 < Real.tanh lam := by simpa using tanh_strictMono hlam
  let x := max 1 (y / Real.tanh lam)
  have hx1 : 1 ≤ x := le_max_left _ _
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hxy : y / Real.tanh lam ≤ x := le_max_right _ _
  have hcosh : x ≤ Real.cosh x := (Real.self_le_sinh_iff.mpr hx0).trans (Real.sinh_lt_cosh (x := x)).le
  have ht2 : Real.tanh lam ≤ Real.tanh (lam*x) :=
    tanh_strictMono.monotone (by nlinarith)
  refine ⟨x, ?_⟩
  have hy : y ≤ x * Real.tanh lam := (div_le_iff₀ ht).mp hxy
  exact hy.trans (mul_le_mul hcosh ht2 ht.le (Real.cosh_pos x).le)

theorem sliceP_surjective {lam : ℝ} (hlam : 0 < lam) : Function.Surjective (sliceP lam) := by
  intro y
  obtain ⟨a, ha⟩ := sliceP_unbounded hlam (-y)
  obtain ⟨b, hb⟩ := sliceP_unbounded hlam y
  exact intermediate_value_univ (-a) b (sliceP_continuous lam)
    ⟨by rw [sliceP_neg]; linarith, hb⟩

theorem sliceQ_surjective {lam : ℝ} (hlam : 0 < lam) : Function.Surjective (sliceQ lam) := by
  intro y
  obtain ⟨x, hx⟩ := sliceP_surjective (inv_pos.mpr hlam) y
  refine ⟨x/lam, ?_⟩
  rw [sliceQ_eq_swapped lam (x/lam) (ne_of_gt hlam)]
  convert hx using 2
  field_simp

theorem sliceP_apply_inv {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    sliceP lam (slicePInv lam y) = y :=
  Function.rightInverse_invFun (sliceP_surjective hlam) y

theorem sliceQ_apply_inv {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    sliceQ lam (sliceQInv lam y) = y :=
  Function.rightInverse_invFun (sliceQ_surjective hlam) y

theorem sliceP_inv_apply {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    slicePInv lam (sliceP lam x) = x :=
  Function.leftInverse_invFun (sliceP_strictMono hlam).injective x

theorem sliceQ_inv_apply {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    sliceQInv lam (sliceQ lam x) = x :=
  Function.leftInverse_invFun (sliceQ_strictMono hlam).injective x

theorem slicePInv_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (slicePInv lam) := by
  intro x y h
  apply (sliceP_strictMono hlam).lt_iff_lt.mp
  simpa only [sliceP_apply_inv hlam] using h

theorem sliceQInv_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (sliceQInv lam) := by
  intro x y h
  apply (sliceQ_strictMono hlam).lt_iff_lt.mp
  simpa only [sliceQ_apply_inv hlam] using h

theorem slicePInv_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (slicePInv lam) :=
  (slicePInv_strictMono hlam).monotone.continuous_of_surjective
    (Function.invFun_surjective (sliceP_strictMono hlam).injective)

theorem sliceQInv_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (sliceQInv lam) :=
  (sliceQInv_strictMono hlam).monotone.continuous_of_surjective
    (Function.invFun_surjective (sliceQ_strictMono hlam).injective)

@[simp] theorem slicePInv_isotropic (y : ℝ) : slicePInv 1 y = Real.arsinh y := by
  apply (sliceP_strictMono (by norm_num : (0:ℝ)<1)).injective
  rw [sliceP_apply_inv (by norm_num), sliceP_isotropic, Real.sinh_arsinh]

@[simp] theorem sliceQInv_isotropic (y : ℝ) : sliceQInv 1 y = Real.arsinh y := by
  apply (sliceQ_strictMono (by norm_num : (0:ℝ)<1)).injective
  rw [sliceQ_apply_inv (by norm_num), sliceQ_isotropic, Real.sinh_arsinh]

@[simp] theorem sliceH_isotropic (y : ℝ) : sliceH 1 y = Real.arsinh (Real.cos y) := by
  simp [sliceH]
@[simp] theorem sliceL_isotropic (y : ℝ) : sliceL 1 y = Real.arsinh |Real.cos y| := by
  simp [sliceL]

end
end IsingBulk.Anisotropic
