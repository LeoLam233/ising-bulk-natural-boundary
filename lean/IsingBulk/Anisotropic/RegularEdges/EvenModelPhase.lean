import IsingBulk.Anisotropic.RegularEdges.EvenPiShift

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.HT.Contour

theorem even_pair_phase_eq_I_inv_pow {N : ℕ} (hN : Even N) :
    (-1:ℂ)^(N.choose 2)=(Complex.I⁻¹)^N := by
  obtain ⟨m,hm⟩ := hN
  have hNm : N=2*m := by omega
  rw [hNm]
  by_cases hm0 : m=0
  · simp [hm0]
  have hc : (2*m).choose 2=m*(2*m-1) := by
    rw [Nat.choose_two_right,show 2*m*(2*m-1)=m*(2*m-1)*2 by ring,Nat.mul_div_cancel]
    norm_num
  have ho : Odd (2*m-1) := ⟨m-1,by omega⟩
  calc
    _ = (-1:ℂ)^m := by rw [hc,Nat.mul_comm m (2*m-1),pow_mul,ho.neg_one_pow]
    _ = ((Complex.I⁻¹)^2)^m := by norm_num
    _ = (Complex.I⁻¹)^(2*m) := (pow_mul _ _ _).symm

theorem edgeAngularDensity_I_scale {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) :
    edgeAngularDensity b B (fun v => Complex.I*S v) u q=
      (Complex.I⁻¹)^N*edgeAngularDensity b B S u q := by
  simp only [edgeAngularDensity,edgeAngularWeight,mul_inv_rev,mul_pow]
  ring

/-- For even particle number the genuine π-shift sign is exactly absorbed by S ↦ iS. -/
theorem complexAngularDensity_negative_even_model {n : ℕ} (hn : Even (n+1))
    {lam b : ℝ} {B S : ℂ→ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : Fin n→ℝ) :
    complexAngularDensity lam z (fun i => (physicalDependentAngles n (fun j => q j+Real.pi) i:ℂ))=
      edgeAngularDensity b B (fun v => Complex.I*S v) u (physicalDependentAngles n q) := by
  rw [complexAngularDensity_negative_even_shift hn hB hS he hu hBi,
    edgeAngularDensity_I_scale,even_pair_phase_eq_I_inv_pow hn]

end
end IsingBulk.Anisotropic.RegularEdges
