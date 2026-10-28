import IsingBulk.HT22.Near.ActualShell
import IsingBulk.HT22.Geometry.SignedShellUpperScale

namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Geometry Set MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

theorem actual_near_dyadic_shell (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ E : ℝ, 1≤E ∧ ∀ a η : ℝ, ∀ n m : ℕ, ∀ ε τ δ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → δ≤δB → ∀ l : ℤ, ∀ i k : Fin (2*n+3),
    (∫⁻ x in signedRightShell a b B δ (preferredDyadicRadius m) l i k,
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal (E^((2*n+3)^2)*
        (preferredDyadicRadius m/Real.sqrt
          (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+preferredDyadicRadius m+ε))^
          (((2*n+3:ℕ):ℝ)^2-2*(j:ℝ)-3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hraw⟩ := actual_near_shell_quadratic b (3*Real.pi+1) (by positivity)
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hraw⟩ := hraw B hB
  refine ⟨min e 1,t,d,lt_min he zero_lt_one,ht,hd,hdB,?_⟩
  intro rcut hrcut hperiod j
  obtain ⟨E,hE,hraw⟩ := hraw rcut hrcut hperiod j
  refine ⟨E,hE,?_⟩
  intro a η n m ε τ δ hε hεr hτ hτr hδ l i k
  by_cases hne : (signedRightShell a b B δ (preferredDyadicRadius m) l i k).Nonempty
  · have hTM := signed_dyadic_shell_scale_le a b B (hδ.trans_lt hdB)
      (hεr.le.trans (min_le_right _ _)) m hne
    apply le_trans ?_ (hraw a η n ε τ (preferredDyadicRadius m) hε
      (hεr.trans_le (min_le_left _ _)) hτ hτr (preferredDyadicRadius_pos m) l hTM i k)
    apply lintegral_mono_set
    intro x hx
    refine ⟨hx.1,⟨?_,hx.2.1.2⟩,hx.2.2⟩
    intro q
    have hh := hx.2.1.1 q
    constructor <;> linarith [hh.1,hh.2]
  · have he : signedRightShell a b B δ (preferredDyadicRadius m) l i k=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he,setLIntegral_empty]
    positivity

end
end IsingBulk.HT22.Near
