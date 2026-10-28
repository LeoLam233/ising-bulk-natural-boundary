import Mathlib.Analysis.Real.Pi.Bounds
import IsingBulk.HT22.Far.ActualShell
import IsingBulk.HT22.Geometry.SignedShellUpperScale

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem norm_le_haar_norm (n : ℕ) (z : ℂ) : ‖z‖≤‖(2*Real.pi:ℂ)^n*z‖ := by
  rw [norm_mul]
  apply le_mul_of_one_le_left (norm_nonneg _)
  rw [norm_pow]
  apply one_le_pow₀
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  linarith [Real.pi_gt_three]

theorem actual_far_unscaled_dyadic_shell (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ δ₀ : ℝ, 0<δ₀ → ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
    ∀ a η : ℝ, ∀ m : ℕ, ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ q : ℕ, ∀ l : ℤ,
    δ₀≤shellCoordinateScale (b.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)) (preferredDyadicRadius q) ε →
    ∀ δ : ℝ, δ≤δB → ∀ i k : Fin (m+3),
    (∫⁻ x in signedRightShell a b B δ (preferredDyadicRadius q) l i k,
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal (farOrderEnvelope A L (m+3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_far_shell_envelope_shrinkable b (3*Real.pi+1) (by positivity)
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨min e 1,t,d,lt_min he zero_lt_one,ht,hd,hdB,?_⟩
  intro δ₀ hδ₀ rcut hrcut hrper j
  obtain ⟨A,L,hA,hsource⟩ := hsource (δ₀^2) (sq_pos_of_pos hδ₀) rcut hrcut hrper j
  refine ⟨A,L,hA,?_⟩
  intro a η m ε τ hε hεr hτ hτr q l hfar δ hδ i k
  by_cases hne : (signedRightShell a b B δ (preferredDyadicRadius q) l i k).Nonempty
  · have hTM := signed_dyadic_shell_scale_le a b B (hδ.trans_lt hdB)
      (hεr.trans_le (min_le_right _ _)).le q hne
    have hdiam := shellCoordinateScale_far_diameter (preferredDyadicRadius_pos q) hε.le hδ₀.le hfar
    have hh := hsource a η m ε τ (preferredDyadicRadius q) hε
      (hεr.trans_le (min_le_left _ _)) hτ hτr hdiam l hTM δ hδ i k
    apply le_trans ?_ hh
    apply lintegral_mono
    intro x
    exact ENNReal.ofReal_le_ofReal (norm_le_haar_norm (m+2) _)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

end
end IsingBulk.HT22.Far
