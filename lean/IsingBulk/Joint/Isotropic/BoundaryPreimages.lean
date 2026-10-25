import IsingBulk.Joint.Isotropic.LowCovering
import IsingBulk.Anisotropic.Geometry.IsotropicBoundary
import IsingBulk.Anisotropic.Geometry.LensBoundary

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

/-- At least one root has modulus at least one; this includes the ramified
boundary values ±i, which must not be discarded by an inverse-function argument. -/
theorem exists_closed_outer_joukowski_root (s : ℂ) :
    ∃ v : ℂ, 1 ≤ ‖v‖ ∧ sinhJoukowski v = s := by
  let a := s+Complex.sqrt (1+s^2)
  let b := s-Complex.sqrt (1+s^2)
  have hsq : (Complex.sqrt (1+s^2))^2 = 1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ)≠0)
  have hab : a*b = -1 := by dsimp [a,b]; linear_combination -hsq
  have ha : a ≠ 0 := by intro h; simp [h] at hab
  have hb : b ≠ 0 := by intro h; simp [h] at hab
  have hja : sinhJoukowski a = s := by
    apply (joukowski_eq_iff ha).mpr
    dsimp [a]
    linear_combination hsq
  have hjb : sinhJoukowski b = s := by
    apply (joukowski_eq_iff hb).mpr
    dsimp [b]
    linear_combination hsq
  by_cases h : 1 ≤ ‖a‖
  · exact ⟨a,h,hja⟩
  · have hn : ‖a‖*‖b‖=1 := by simpa only [norm_mul,norm_neg,norm_one] using congrArg norm hab
    refine ⟨b,?_,hjb⟩
    have ha' := lt_of_not_ge h
    nlinarith [norm_nonneg a,norm_nonneg b]

theorem unit_preimage_low (s : ℂ) (hs : ‖s‖ = 1) :
    ∃ z ∈ frontier (omegaL 1), Complex.sinh z = s := by
  obtain ⟨v,hv,hvs⟩ := exists_closed_outer_joukowski_root s
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  let z := Complex.log v
  have hzre : 0 ≤ z.re := by rw [Complex.log_re]; exact Real.log_nonneg hv
  have hz : Complex.sinh z = s := by rw [sinh_eq_joukowski_exp,Complex.exp_log hv0,hvs]
  refine ⟨z,?_,hz⟩
  rw [mem_frontier_omegaL_iff (by norm_num : (0:ℝ)<1),sliceL_isotropic]
  apply Real.sinh_injective
  rw [Real.sinh_arsinh]
  have hn := norm_sinh_sq z
  rw [hz,hs] at hn
  have ht := Real.sin_sq_add_cos_sq z.im
  have ha := sq_abs (Real.cos z.im)
  have hp : 0 ≤ Real.sinh z.re := Real.sinh_nonneg_iff.mpr hzre
  nlinarith [abs_nonneg (Real.cos z.im)]

theorem unit_sinh_frontier_high {z : ℂ} (hi : |z.im| ≤ Real.pi/2)
    (hs : ‖Complex.sinh z‖ = 1) : z ∈ frontier (omegaH 1) := by
  rw [mem_frontier_omegaH_iff (by norm_num : (0:ℝ)<1)]
  have hy : sliceY 1 = Real.pi/2 := by norm_num [sliceY]
  rw [hy,sliceH_isotropic]
  refine ⟨hi,?_⟩
  apply Real.sinh_injective
  rw [Real.sinh_arsinh,←Real.abs_sinh]
  have hc : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc (abs_le.mp hi)
  have hn := norm_sinh_sq z
  rw [hs] at hn
  have ht := Real.sin_sq_add_cos_sq z.im
  nlinarith [sq_abs (Real.sinh z.re),abs_nonneg (Real.sinh z.re)]

theorem unit_preimage_high (s : ℂ) (hs : ‖s‖ = 1) :
    ∃ z ∈ frontier (omegaH 1), Complex.sinh z = s := by
  by_cases hre : s.re = 0
  · have hn : s.im^2 = 1 := by
      have hh : s.re^2+s.im^2 = 1 := by
        simpa only [Complex.normSq_apply,Complex.normSq_eq_norm_sq,hs,pow_two] using
          (show Complex.normSq s = 1 by rw [Complex.normSq_eq_norm_sq,hs]; norm_num)
      nlinarith
    rcases sq_eq_one_iff.mp hn with him | him
    · have he : s = Complex.I := Complex.ext (by simpa using hre) (by simpa using him)
      let z : ℂ := (Real.pi/2:ℝ)*Complex.I
      have hz : Complex.sinh z = s := by
        rw [he]
        dsimp [z]
        rw [Complex.sinh_mul_I]
        norm_cast
        simp
      refine ⟨z,unit_sinh_frontier_high ?_ (by rwa [hz]),hz⟩
      simp [z,abs_of_pos (half_pos Real.pi_pos)]
    · have he : s = -Complex.I := Complex.ext (by simpa using hre) (by simpa using him)
      let z : ℂ := -(Real.pi/2:ℝ)*Complex.I
      have hz : Complex.sinh z = s := by
        rw [he]
        dsimp [z]
        rw [neg_mul,Complex.sinh_neg,Complex.sinh_mul_I]
        norm_cast
        simp
      refine ⟨z,unit_sinh_frontier_high ?_ (by rwa [hz]),hz⟩
      simp [z,abs_of_pos (half_pos Real.pi_pos)]
  · have hi : |s.im| < 1 := by simpa only [hs] using Complex.abs_im_lt_norm.mpr hre
    have hz := sinh_arsinhRight_strip hi
    refine ⟨IsingBulk.Final.arsinhRight s,unit_sinh_frontier_high ?_ (by rwa [hz]),hz⟩
    rw [IsingBulk.Final.arsinhRight,Complex.log_im]
    exact (Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (IsingBulk.HT.Final.temperature_log_argument_re_pos hi))).le

end
end IsingBulk.Joint
