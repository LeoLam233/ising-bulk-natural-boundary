import IsingBulk.Preferred22.RootContinuation

/-! Quantitative movement of the actual center-selected physical sheet.
The relative root bound will preserve both pair denominators and the full
product gap on the selected parameter disk. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1000000

lemma preferred_sqrt_sub_one_norm (z : ℂ) : ‖Complex.sqrt z-1‖≤‖z-1‖ := by
  have hre := IsingBulk.Branch.sqrt_re_nonneg_all z
  have hn := Complex.re_le_norm (Complex.sqrt z+1)
  simp only [Complex.add_re,Complex.one_re] at hn
  have hden : 1≤‖Complex.sqrt z+1‖ := by linarith
  have he : (Complex.sqrt z-1)*(Complex.sqrt z+1)=z-1 := by
    have h := complex_sqrt_sq z
    linear_combination h
  have hm := congrArg (fun w : ℂ => ‖w‖) he
  rw [norm_mul] at hm
  nlinarith [norm_nonneg (Complex.sqrt z-1)]

lemma preferred_physical_root_inverse_bound {W : ℂ} {R : ℝ}
    (hW : OffRealSegment W) (hn : ‖W‖≤R) :
    ‖(physicalRoot W)⁻¹‖≤2*R+1 := by
  have he : (physicalRoot W)⁻¹=2*W-physicalRoot W := by
    linear_combination physicalRoot_trace W
  rw [he]
  have h := norm_sub_le (2*W) (physicalRoot W)
  rw [norm_mul,Complex.norm_ofNat] at h
  linarith [physicalRoot_inside hW]

/-- Source-independent algebraic estimate for the literal continuation of
a physical center root. Only the actual dispersion norm and discriminant
margin are used; the continued root need not remain the global interior root. -/
theorem preferred_local_root_relative_bound {W V : ℂ} {R D : ℝ}
    (hR : 0≤R) (hW : OffRealSegment W) (hWnorm : ‖W‖≤R)
    (hD : 0<D) (hD1 : D≤1) (hgap : D≤‖W^2-1‖) (hsmall : ‖V-W‖≤1) :
    ‖localPhysicalRoot W V/physicalRoot W-1‖≤
      ((2*R+1)*(2*R+2))*‖V-W‖/Real.sqrt D := by
  let z := physicalRoot W
  let A := ‖W^2-1‖
  let a := Real.sqrt A
  let d := Real.sqrt D
  let K := 2*R+1
  have hA : 0<A := hD.trans_le hgap
  have ha : 0<a := Real.sqrt_pos.mpr hA
  have hd : 0<d := Real.sqrt_pos.mpr hD
  have hK : 0<K := by dsimp only [K]; positivity
  have hDne : W^2-1≠0 := norm_pos_iff.mp hA
  have hz : z≠0 := physicalRoot_ne_zero W
  have hasq : a^2=A := Real.sq_sqrt hA.le
  have hda : d≤a := Real.sqrt_le_sqrt hgap
  have hd1 : d≤1 := (Real.sqrt_le_sqrt hD1).trans_eq (by norm_num)
  have hzn : ‖z-W‖=a := by
    have h := congrArg (fun w : ℂ => ‖w‖) (physicalRoot_discriminant W)
    rw [norm_pow] at h
    change ‖z-W‖^2=A at h
    calc
      _ = Real.sqrt (‖z-W‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = a := congrArg Real.sqrt h
  have hsum : ‖V+W‖≤K := by
    have he : V+W=(V-W)+2*W := by ring
    rw [he]
    have h := norm_add_le (V-W) (2*W)
    rw [norm_mul,Complex.norm_ofNat] at h
    dsimp only [K]
    linarith
  let Q := (V^2-1)/(W^2-1)
  have hratio : ‖Q-1‖≤‖V-W‖*K/A := by
    have he : Q-1=(V-W)*(V+W)/(W^2-1) := by
      dsimp only [Q]
      field_simp
      ring
    rw [he,norm_div,norm_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)) hA.le
  have hdiff : ‖localPhysicalRoot W V-z‖≤‖V-W‖*(1+K/a) := by
    have he : localPhysicalRoot W V-z=(V-W)+(z-W)*(Complex.sqrt Q-1) := by
      dsimp only [localPhysicalRoot,Q,z]
      ring
    rw [he]
    calc
      _ ≤ ‖V-W‖+‖z-W‖*‖Complex.sqrt Q-1‖ := by
        simpa only [norm_mul] using norm_add_le (V-W) ((z-W)*(Complex.sqrt Q-1))
      _ ≤ ‖V-W‖+a*(‖V-W‖*K/A) := by
        rw [hzn]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          ((preferred_sqrt_sub_one_norm Q).trans hratio) ha.le)
      _ = ‖V-W‖*(1+K/a) := by
        field_simp
        linear_combination ‖V-W‖*K*hasq
  have hcoef : 1+K/a≤(K+1)/d := by
    have hdiv : K/a≤K/d := div_le_div_of_nonneg_left hK.le hd hda
    have h1 : 1≤1/d := (le_div_iff₀ hd).mpr (by simpa using hd1)
    calc
      _ ≤ 1/d+K/d := add_le_add h1 hdiv
      _ = (K+1)/d := by ring
  have hfinal : ‖localPhysicalRoot W V-z‖≤‖V-W‖*((K+1)/d) :=
    hdiff.trans (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _))
  have he : localPhysicalRoot W V/z-1=(localPhysicalRoot W V-z)*z⁻¹ := by
    field_simp
  rw [he,norm_mul]
  have hinv : ‖z⁻¹‖≤K := preferred_physical_root_inverse_bound hW hWnorm
  calc
    _ ≤ (‖V-W‖*((K+1)/d))*K := mul_le_mul hfinal hinv (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [K,d]; ring

end
end IsingBulk.Preferred22
