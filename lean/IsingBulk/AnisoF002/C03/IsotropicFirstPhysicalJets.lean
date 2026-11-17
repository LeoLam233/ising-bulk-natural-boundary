import IsingBulk.AnisoF002.C03.IsotropicFirstDirectionalJets

/-!
# Derivative bounds for the original isotropic first-chart quotient

Exact differentiation of the directional filling transfers the compact
jet bounds back to the physical radial parameter. The full squared
Vandermonde remains a parameter-independent factor in the density.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstUnscaledRatio {N : ℕ} (α : ℝ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ)) : ℂ :=
  isotropicFirstAmplitude α σ p / isotropicFirstDenominator α σ p

theorem isotropicFirstFilledRatio_exact {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s t : ℂ) (hs : s ≠ 0) :
    s ^ 2 * isotropicFirstUnscaledRatio α σ (s ^ 2 * t, fun i => s * x i) =
      isotropicFirstFilledRatio α σ x (s, t) := by
  rw [isotropicFirstUnscaledRatio, isotropicFirstDenominator_blowup hα hπ σ hres x hx]
  unfold isotropicFirstFilledRatio
  field_simp

theorem isotropicFirstFilledRatio_jet_exact {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s t : ℂ) (hs : s ≠ 0) (j : ℕ) :
    s ^ (2 * j + 2) *
      iteratedDeriv j (fun h => isotropicFirstUnscaledRatio α σ
        (h, fun i => s * x i)) (s ^ 2 * t) =
      iteratedDeriv j (fun v => isotropicFirstFilledRatio α σ x (s, t + v)) 0 := by
  have he : (fun v => s ^ 2 * isotropicFirstUnscaledRatio α σ
      (s ^ 2 * (t + v), fun i => s * x i)) =
      fun v => isotropicFirstFilledRatio α σ x (s, t + v) := by
    funext v
    exact isotropicFirstFilledRatio_exact hα hπ σ hres x hx s (t + v) hs
  have hj := congrArg (fun f : ℂ → ℂ => iteratedDeriv j f 0) he
  rw [iteratedDeriv_const_mul_field] at hj
  change s ^ 2 * iteratedDeriv j
    (fun v => (fun u => isotropicFirstUnscaledRatio α σ
      (s ^ 2 * u, fun i => s * x i)) (t + v)) 0 = _ at hj
  have hshift : iteratedDeriv j
      (fun v => (fun u => isotropicFirstUnscaledRatio α σ
        (s ^ 2 * u, fun i => s * x i)) (t + v)) 0 =
      iteratedDeriv j (fun u => isotropicFirstUnscaledRatio α σ
        (s ^ 2 * u, fun i => s * x i)) t := by
    simpa only [add_zero] using congrFun
      (iteratedDeriv_comp_const_add (n := j)
        (f := fun u => isotropicFirstUnscaledRatio α σ (s ^ 2 * u, fun i => s * x i)) (s := t)) 0
  rw [hshift,
    iteratedDeriv_comp_mul_unconditional j
      (fun h => isotropicFirstUnscaledRatio α σ (h, fun i => s * x i)) (s ^ 2) t,
    ← pow_mul, ← mul_assoc, ← pow_add] at hj
  convert hj using 1
  congr 2
  omega

theorem exists_isotropic_first_actual_quotient_jet_bound {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1) (j : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ e : ℝ, 0 < e →
      ∀ u : Fin N → ℝ, (∑ i, u i) = 0 → e + ∑ i, u i ^ 2 < δ →
      ‖iteratedDeriv j (fun h => isotropicFirstUnscaledRatio α σ
        (h, fun i => (u i : ℂ))) (isotropicRadialParameter α e - (2 * Real.cos α : ℂ))‖ ≤
          C / (e + ∑ i, u i ^ 2) ^ (j + 1) := by
  obtain ⟨d, C, hd, hC, hbound⟩ := exists_uniform_isotropic_first_directional_jets hN hα hhalf σ j
  refine ⟨d ^ 2, C, sq_pos_of_pos hd, hC, ?_⟩
  intro e he u hu hsmall
  let Q := ∑ i, u i ^ 2
  let s := Real.sqrt (e + Q)
  let weight := e / (e + Q)
  let x : Fin N → ℝ := fun i => u i / s
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 < e + Q := add_pos_of_pos_of_nonneg he hQ
  have hs : 0 < s := Real.sqrt_pos.2 hE
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : s ^ 2 = e + Q := Real.sq_sqrt hE.le
  have hsw : s ^ 2 * weight = e := by dsimp only [weight]; rw [hs2]; field_simp
  have hsd : |s| < d := by rw [abs_of_pos hs]; nlinarith
  have hxsum : ∑ i, (x i : ℂ) = 0 := by
    simp only [x, Complex.ofReal_div, ← Finset.sum_div, ← Complex.ofReal_sum, hu,
      Complex.ofReal_zero, zero_div]
  have hscale (i : Fin N) : (s : ℂ) * (x i : ℂ) = (u i : ℂ) := by
    dsimp only [x]
    rw [Complex.ofReal_div]
    field_simp
  have hswc : (s : ℂ) ^ 2 * (weight : ℂ) = (e : ℂ) := by exact_mod_cast hsw
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hh := isotropicFirstFilledRatio_jet_exact hα hπ σ hres
    (fun i => (x i : ℂ)) hxsum (s : ℂ)
      ((weight : ℂ) * isotropicRadialIncrement α ((s : ℂ) ^ 2 * (weight : ℂ))) hsc j
  have hb := hbound s hsd (weight, x) (isotropic_first_normalized_direction he u)
  have hepar : (s : ℂ) ^ 2 *
      ((weight : ℂ) * isotropicRadialIncrement α ((s : ℂ) ^ 2 * (weight : ℂ))) =
      isotropicRadialParameter α e - (2 * Real.cos α : ℂ) := by
    rw [← mul_assoc, hswc, isotropicRadialParameter_filled α e (by linarith)]
  simp only [hscale, hepar] at hh
  change ‖iteratedDeriv j (fun v => isotropicFirstFilledRatio α σ (fun i => (x i : ℂ))
    ((s : ℂ), (weight : ℂ) * isotropicRadialIncrement α ((s : ℂ) ^ 2 * (weight : ℂ)) + v)) 0‖ ≤ C at hb
  rw [← hh, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at hb
  have hp : s ^ (2 * j + 2) = (e + Q) ^ (j + 1) := by
    rw [show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul, hs2]
  rw [hp] at hb
  exact (le_div_iff₀ (pow_pos hE _)).2 (by simpa only [mul_comm] using hb)

end
end IsingBulk.AnisoF002.Isotropic
