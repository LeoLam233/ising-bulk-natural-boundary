import IsingBulk.AnisoF002.C03.IsotropicSignedCoefficient

/-!
# Every physical isotropic jet under the signed conjugation

The identity is local on the genuine upper parameter half-plane. The
same exact transformation is provided in the original exterior variable
t, with S=t+t^{-1}. No holomorphy of complex conjugation alone is used:
the twice-conjugated function is differentiated exactly.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology ComplexConjugate
open Set Filter

theorem isotropic_iteratedDeriv_twice_conjugated (j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv j (fun z => conj (f (conj z))) =
      fun z => conj (iteratedDeriv j f (conj z)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact deriv_conj_conj (f := iteratedDeriv j f)

theorem isotropic_iteratedDeriv_negative_conjugated (j : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    iteratedDeriv j (fun w => conj (f (-conj w))) z =
      (-1 : ℂ) ^ j * conj (iteratedDeriv j f (-conj z)) := by
  have he : (fun w => conj (f (-conj w))) =
      fun w => (fun v => conj (f (conj v))) (-w) := by
    funext w
    simp only [map_neg]
  rw [he]
  have hh := iteratedDeriv_comp_neg j (fun v : ℂ => conj (f (conj v))) z
  rw [isotropic_iteratedDeriv_twice_conjugated] at hh
  simpa only [map_neg, smul_eq_mul] using hh

theorem isotropic_iteratedDeriv_signed_negative_germ {f g : ℂ → ℂ} {z : ℂ}
    (he : f =ᶠ[𝓝 (-conj z)] fun w => -conj (g (-conj w))) (j : ℕ) :
    iteratedDeriv j f (-conj z) = (-1 : ℂ) ^ (j + 1) * conj (iteratedDeriv j g z) := by
  rw [(he.iteratedDeriv j).eq_of_nhds, iteratedDeriv_fun_neg,
    isotropic_iteratedDeriv_negative_conjugated]
  simp only [map_neg, starRingEnd_self_apply, neg_neg, pow_succ]
  ring

theorem isotropic_odd_coefficient_neg_conj_jets (m j : ℕ) {S : ℂ} (hS : 0 < S.im) :
    iteratedDeriv j (isotropicFullParticleCoefficient (2 * m) 0 1) (-conj S) =
      (-1 : ℂ) ^ (j + 1) *
        conj (iteratedDeriv j (isotropicFullParticleCoefficient (2 * m) Real.pi (-1)) S) := by
  apply isotropic_iteratedDeriv_signed_negative_germ ?_ j
  have hu : 0 < (-conj S).im := by simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hS
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu] with T hT
  have hTc : 0 < (-conj T).im := by simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hT
  simpa only [map_neg, starRingEnd_self_apply, neg_neg] using isotropic_odd_coefficient_neg_conj m hTc

theorem isotropic_even_coefficient_neg_conj_jets (m j : ℕ) {S : ℂ} (hS : 0 < S.im) :
    iteratedDeriv j (isotropicFullParticleCoefficient (2 * m + 1) 0 1) (-conj S) =
      (-1 : ℂ) ^ j *
        conj (iteratedDeriv j (isotropicFullParticleCoefficient (2 * m + 1) 0 1) S) := by
  have hu : 0 < (-conj S).im := by simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hS
  have he : isotropicFullParticleCoefficient (2 * m + 1) 0 1 =ᶠ[𝓝 (-conj S)]
      fun w => conj (isotropicFullParticleCoefficient (2 * m + 1) 0 1 (-conj w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu] with T hT
    have hTc : 0 < (-conj T).im := by simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hT
    simpa only [map_neg, starRingEnd_self_apply, neg_neg] using isotropic_even_coefficient_neg_conj m hTc
  rw [(he.iteratedDeriv j).eq_of_nhds, isotropic_iteratedDeriv_negative_conjugated]
  simp only [map_neg, starRingEnd_self_apply, neg_neg]

def isotropicExteriorParticleCoefficient (n : ℕ) (a : ℝ) (σ t : ℂ) : ℂ :=
  isotropicFullParticleCoefficient n a σ (t + t⁻¹)

theorem isotropic_exterior_parameter_neg_conj (t : ℂ) :
    -conj t + (-conj t)⁻¹ = -conj (t + t⁻¹) := by
  simp only [inv_neg, map_add, map_inv₀, neg_add_rev]
  ring

theorem isotropic_exterior_parameter_ne_zero {t : ℂ} (h : 0 < (t + t⁻¹).im) : t ≠ 0 := by
  intro ht
  simp only [ht, inv_zero, add_zero, Complex.zero_im] at h
  exact (lt_irrefl 0) h

theorem isotropic_odd_exterior_coefficient_neg_conj (m : ℕ) {t : ℂ}
    (ht : 0 < (t + t⁻¹).im) :
    isotropicExteriorParticleCoefficient (2 * m) 0 1 (-conj t) =
      -conj (isotropicExteriorParticleCoefficient (2 * m) Real.pi (-1) t) := by
  unfold isotropicExteriorParticleCoefficient
  rw [isotropic_exterior_parameter_neg_conj]
  exact isotropic_odd_coefficient_neg_conj m ht

theorem isotropic_odd_exterior_coefficient_neg_conj_jets (m j : ℕ) {t : ℂ}
    (ht : 0 < (t + t⁻¹).im) :
    iteratedDeriv j (isotropicExteriorParticleCoefficient (2 * m) 0 1) (-conj t) =
      (-1 : ℂ) ^ (j + 1) *
        conj (iteratedDeriv j (isotropicExteriorParticleCoefficient (2 * m) Real.pi (-1)) t) := by
  apply isotropic_iteratedDeriv_signed_negative_germ ?_ j
  have hu : 0 < ((-conj t) + (-conj t)⁻¹).im := by
    rw [isotropic_exterior_parameter_neg_conj]
    simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using ht
  have hn := isotropic_exterior_parameter_ne_zero hu
  have hc : ContinuousAt (fun w : ℂ => (w + w⁻¹).im) (-conj t) :=
    Complex.continuous_im.continuousAt.comp (continuousAt_id.add (continuousAt_id.inv₀ hn))
  filter_upwards [hc.eventually (isOpen_Ioi.mem_nhds hu)] with w hw
  have hwc : 0 < ((-conj w) + (-conj w)⁻¹).im := by
    rw [isotropic_exterior_parameter_neg_conj]
    simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hw
  simpa only [map_neg, starRingEnd_self_apply, neg_neg] using isotropic_odd_exterior_coefficient_neg_conj m hwc

theorem isotropicExteriorRadial_neg_conj (α ε : ℝ) :
    isotropicExteriorRadial (Real.pi - α) ε = -conj (isotropicExteriorRadial α ε) := by
  simp only [isotropicExteriorRadial, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub, Complex.ofReal_neg,
    map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem isotropicRadialParameter_neg_conj (α ε : ℝ) :
    isotropicRadialParameter (Real.pi - α) ε = -conj (isotropicRadialParameter α ε) := by
  unfold isotropicRadialParameter
  rw [isotropicExteriorRadial_neg_conj, isotropic_exterior_parameter_neg_conj]

end IsingBulk.AnisoF002.Isotropic
