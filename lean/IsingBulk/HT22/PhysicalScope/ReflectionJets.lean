import IsingBulk.HT22.Physical.Symmetries
import IsingBulk.HT.Contour.SignedReflectionJets
import IsingBulk.HT22.Arithmetic.BranchCharts

/-! Exact derivatives of the original physical coefficients under the
signed negative/conjugate coordinate reflection. No evenness is assumed. -/
namespace IsingBulk.HT22.PhysicalScope
noncomputable section
open Physical Filter
open scoped Topology

theorem signedCoefficient_iteratedDeriv_conjugate (negative : Bool) (N j : ℕ)
    {t : ℂ} (ht : 1<‖t‖) :
    iteratedDeriv j (signedCoefficient negative N) (star t)=
      star (iteratedDeriv j (signedCoefficient negative N) t) := by
  have hts : 1<‖star t‖ := by simpa only [norm_star] using ht
  have he : signedCoefficient negative N=ᶠ[𝓝 (star t)]
      (star ∘ signedCoefficient negative N ∘ star) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hts] with z hz
    have hh := congrArg star (signedCoefficient_conj negative N hz)
    simpa only [Function.comp_def,star_star] using hh.symm
  rw [he.iteratedDeriv_eq j,IsingBulk.HT.Contour.iteratedDeriv_star_conj]
  simp only [Function.comp_def,star_star]

theorem signed_negative_reflected_derivative (n j : ℕ) {t : ℂ} (ht : 1<‖t‖) :
    iteratedDeriv j (signedCoefficient true (2*n+1)) (-star t)=
      -((-1:ℂ)^j*star (iteratedDeriv j (coefficient (2*n+1)) t)) := by
  rw [negativeCoefficient_iteratedDeriv n j (by simpa only [norm_neg,norm_star] using ht),neg_neg]
  have hh := signedCoefficient_iteratedDeriv_conjugate false (2*n+1) j ht
  change iteratedDeriv j (coefficient (2*n+1)) (star t)=
    star (iteratedDeriv j (coefficient (2*n+1)) t) at hh
  rw [hh]

theorem signed_negative_reflected_derivative_involution (n j : ℕ) {t : ℂ} (ht : 1<‖t‖) :
    -((-1:ℂ)^j*star (iteratedDeriv j (signedCoefficient true (2*n+1)) (-star t)))=
      iteratedDeriv j (coefficient (2*n+1)) t := by
  rw [signed_negative_reflected_derivative n j ht]
  simp only [star_neg,star_mul',star_pow,star_one,star_star,mul_neg,neg_neg]
  have he : (-1:ℂ)^j*(-1:ℂ)^j=1 := by rw [←mul_pow];norm_num
  rw [←mul_assoc,he,one_mul]

theorem signed_negative_reflected_derivative_norm (n j : ℕ) {t : ℂ} (ht : 1<‖t‖) :
    ‖iteratedDeriv j (signedCoefficient true (2*n+1)) (-star t)‖=
      ‖iteratedDeriv j (coefficient (2*n+1)) t‖ := by
  rw [signed_negative_reflected_derivative n j ht]
  simp only [norm_neg,norm_mul,norm_pow,norm_one,one_pow,one_mul,norm_star]

end
end IsingBulk.HT22.PhysicalScope
