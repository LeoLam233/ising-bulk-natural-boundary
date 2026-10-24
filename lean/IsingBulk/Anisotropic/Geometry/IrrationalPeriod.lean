import IsingBulk.Anisotropic.Geometry.Periodicity
import IsingBulk.Anisotropic.Geometry.AxisExchange

namespace IsingBulk.Anisotropic
noncomputable section

/-- Exchange the axes without identifying a susceptibility period. -/
theorem ImaginarySpectralPeriod.axis_exchange {lam t : ℝ} (hlam : lam≠0)
    (hp : ImaginarySpectralPeriod lam t) : ImaginarySpectralPeriod (lam⁻¹) (lam*t) := by
  intro z
  let w : ℂ := ((lam⁻¹:ℝ):ℂ)*z
  have hw : (lam:ℂ)*w=z := by
    dsimp only [w]
    rw [Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hlam),one_mul]
  have hs : (lam:ℂ)*(w+(t:ℂ)*Complex.I)=z+((lam*t:ℝ):ℂ)*Complex.I := by
    rw [mul_add,hw,Complex.ofReal_mul]
    ring
  calc
    _ ↔ (lam:ℂ)*(w+(t:ℂ)*Complex.I)∈spectralSet (lam⁻¹) := by rw [hs]
    _ ↔ w+(t:ℂ)*Complex.I∈spectralSet lam := mem_spectralSet_axis_exchange_iff hlam _
    _ ↔ w∈spectralSet lam := hp w
    _ ↔ (lam:ℂ)*w∈spectralSet (lam⁻¹) := (mem_spectralSet_axis_exchange_iff hlam _).symm
    _ ↔ z∈spectralSet (lam⁻¹) := by rw [hw]

/-- An irrational-frequency cosine cannot vanish at two arguments separated
by pi. This is the finite arithmetic core of the no-period argument. -/
theorem irrational_cos_pair_not_both_zero {lam : ℝ} (hlam : Irrational lam) (y : ℝ)
    (h0 : Real.cos (lam*y)=0) (h1 : Real.cos (lam*(y+Real.pi))=0) : False := by
  obtain ⟨k,hk⟩ := Real.cos_eq_zero_iff.mp h0
  obtain ⟨l,hl⟩ := Real.cos_eq_zero_iff.mp h1
  have he : lam*Real.pi=((l-k:ℤ):ℝ)*Real.pi := by
    push_cast
    linarith
  have hh : lam=((l-k:ℤ):ℝ) := (mul_right_cancel₀ Real.pi_ne_zero) he
  exact hlam.ne_int (l-k) hh

/-- A period of the union of the two irrationally-spaced axis progressions
must preserve the first progression. Two consecutive test points suffice. -/
theorem ImaginarySpectralPeriod.eq_int_pi {lam t : ℝ} (hlam : Irrational lam)
    (hp : ImaginarySpectralPeriod lam t) : ∃k : ℤ,t=k*Real.pi := by
  have haxis (y : ℝ) (hy : Real.cos y=0) :
      Real.cos (y+t)=0 ∨ Real.cos (lam*(y+t))=0 := by
    have hz : (y:ℂ)*Complex.I∈spectralSet lam :=
      (imaginary_mem_spectralSet_iff lam y).mpr (by rw [hy,zero_mul])
    have ht := (hp ((y:ℂ)*Complex.I)).mpr hz
    have he : (y:ℂ)*Complex.I+(t:ℂ)*Complex.I=((y+t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [he,imaginary_mem_spectralSet_iff] at ht
    exact mul_eq_zero.mp ht
  have h0 := haxis (Real.pi/2) Real.cos_pi_div_two
  have h1 := haxis (Real.pi/2+Real.pi) (by rw [Real.cos_add_pi,Real.cos_pi_div_two,neg_zero])
  have ht : Real.cos (Real.pi/2+t)=0 := by
    rcases h0 with h0|h0
    · exact h0
    · rcases h1 with h1|h1
      · have he : Real.pi/2+Real.pi+t=(Real.pi/2+t)+Real.pi := by ring
        rw [he,Real.cos_add_pi] at h1
        exact neg_eq_zero.mp h1
      · exact (irrational_cos_pair_not_both_zero hlam (Real.pi/2+t) h0
          (by convert h1 using 2; ring)).elim
  obtain ⟨k,hk⟩ := Real.cos_eq_zero_iff.mp ht
  exact ⟨k,by linarith⟩

/-- For every irrational positive ratio, the entire spectral set has no
nonzero imaginary period. This does not assert a period for a physical sum. -/
theorem irrational_imaginary_spectral_period_eq_zero {lam t : ℝ}
    (hlam : Irrational lam) (hp : ImaginarySpectralPeriod lam t) : t=0 := by
  obtain ⟨k,hk⟩ := hp.eq_int_pi hlam
  obtain ⟨l,hl⟩ := (hp.axis_exchange hlam.ne_zero).eq_int_pi hlam.inv
  by_cases hk0 : k=0
  · simpa only [hk0,Int.cast_zero,zero_mul] using hk
  have he : lam*(k:ℝ)=(l:ℝ) := by
    apply (mul_right_cancel₀ Real.pi_ne_zero)
    rw [mul_assoc,←hk]
    exact hl
  exact ((hlam.mul_intCast hk0).ne_int l he).elim

end
end IsingBulk.Anisotropic
