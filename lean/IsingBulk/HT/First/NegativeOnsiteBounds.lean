import IsingBulk.HT.Final.OnsiteSymmetry
import IsingBulk.HT.Contour.SignedReflectionJets
import IsingBulk.First.OnsiteGlobalBound

/-! The actual onsite observable has a proved all-N parity, unlike the full
odd HT susceptibility. Its exact reflected-jet norms transfer the positive
onsite radial bound to every negative level in (−2,0). -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.First IsingBulk.HT.Final IsingBulk.HT.Contour
open scoped Topology

theorem onsiteFormFactor_reflected_iteratedDeriv_norm (N j : ℕ) (r : ℝ) (s : ℂ) :
    ‖iteratedDeriv j (onsiteFormFactor N r) (-star s)‖ =
      ‖iteratedDeriv j (onsiteFormFactor N r) s‖ := by
  have hsign : (-1:ℂ)^N*(-1:ℂ)^N = 1 := by rw [← mul_pow]; norm_num
  have hf : onsiteFormFactor N r =
      (fun z => (-1:ℂ)^N*star (onsiteFormFactor N r (-star z))) := by
    funext z
    rw [onsiteFormFactor_neg,onsiteFormFactor_conjugate]
    simp only [star_mul',star_pow,star_neg,star_one,star_star]
    rw [← mul_assoc,hsign,one_mul]
  have hj := congrArg (fun f : ℂ → ℂ => iteratedDeriv j f (-star s)) hf
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_star_neg_conj] at hj
  simp only [star_neg,star_star,neg_neg] at hj
  rw [hj]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,norm_star,one_mul]

theorem negative_onsite_global_radial_bound {N : ℕ} (hN : 0 < N)
    (level : ℝ) (hlevel : -2 < level ∧ level < 0)
    (theta : ℝ) (htheta : 0 < Real.sin theta)
    (hS : sourceS (exp ((theta:ℂ)*I)) = (level:ℂ)) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ‖(deriv^[j] (onsiteFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C := by
  let phi := Real.pi-theta
  have hsine : Real.sin phi = Real.sin theta := Real.sin_pi_sub theta
  have hphi : 0 < Real.sin phi := by rwa [hsine]
  have hreflect : exp ((phi:ℂ)*I) = -star (exp ((theta:ℂ)*I)) := by
    simpa [phi, IsingBulk.Branch.radialParameter] using
      radialParameter_neg_conjugate theta 0
  have htrace : sourceS (exp ((phi:ℂ)*I)) = ((-level:ℝ):ℂ) := by
    rw [hreflect,sourceS_neg,sourceS_conjugate,hS]
    simp
  obtain ⟨e,he,hB⟩ := onsite_global_radial_bound hN (-level)
    (by constructor <;> linarith) phi hphi htrace
  refine ⟨e,he,?_⟩
  intro j
  obtain ⟨C,hC,hb⟩ := hB j
  refine ⟨C,hC,?_⟩
  intro epsilon heps hee
  have hrad : (sourceRadialPair phi epsilon).1 = (sourceRadialPair theta epsilon).1 := by
    simp only [sourceRadialPair,hsine]
  have hpoint : (sourceRadialPair phi epsilon).2 = -star (sourceRadialPair theta epsilon).2 :=
    radialParameter_neg_conjugate theta epsilon
  have hh := hb epsilon heps hee
  rw [hrad,hpoint,← iteratedDeriv_eq_iterate,onsiteFormFactor_reflected_iteratedDeriv_norm,
    iteratedDeriv_eq_iterate] at hh
  exact hh

end
end IsingBulk.HT.First
