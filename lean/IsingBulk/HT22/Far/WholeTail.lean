import IsingBulk.HT22.Far.WholeMass
import IsingBulk.HT22.Tail.ExponentArithmetic

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def wholeTransportedIntegral (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (rcut : ℝ → ℝ) (j : ℕ) (a η : ℝ) (n : ℕ) (ε τ : ℝ) : ℂ :=
  ∫ x : Fin (2*n+2) → ℝ in angularBox (2*n+2),
    transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ preferredPopulationCutoff B.p B.m rcut j
      (IsingBulk.Branch.radialParameter b.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAtTotal a x))

def wholeTransportedMass (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (rcut : ℝ → ℝ) (j : ℕ) (a η : ℝ) (n : ℕ) (ε τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Fin (2*n+2) → ℝ in angularBox (2*n+2), ENNReal.ofReal
    ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ preferredPopulationCutoff B.p B.m rcut j
      (IsingBulk.Branch.radialParameter b.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖

theorem high_odd_order_ge {p : ℕ} (hp : Odd p) (n : ℕ) :
    p+2≤2*(p/2+n)+3 := by
  obtain ⟨q,hq⟩ := hp
  omega

theorem actual_high_odd_mass_sum (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ p : ℕ, 5≤p → Odd p → ∀ j : ℕ, j≤IsingBulk.HT.First.derivativeOrder p →
    ∃ C : ℝ, 0<C ∧ ∀ a η : ℝ, |a|≤Real.pi → ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ δ : ℝ, δ≤δB → PreferredRightCutoffData b B δ rcut →
    (∑' n,wholeTransportedMass b B rcut j a η (p/2+n) ε τ)≤ENNReal.ofReal (C*(1+|Real.log ε|)) ∧
    Summable (fun n => ‖wholeTransportedIntegral b B rcut j a η (p/2+n) ε τ‖) ∧
    (∑' n,‖wholeTransportedIntegral b B rcut j a η (p/2+n) ε τ‖)≤C*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_whole_angular_mass b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro rcut hrcut hrper p _hp5 hp j hj
  obtain ⟨H,A,L,hH,hA,hsource⟩ := hsource rcut hrcut hrper j
  let W : ℕ → ℝ := fun n => completeOrderEnvelope H A L (2*(p/2+n)+3)
  have hW (n : ℕ) : 0≤W n := completeOrderEnvelope_nonneg hH.le hA.le _ _
  have hsum : Summable W := (completeOrderEnvelope_summable H hA.le L).comp_injective
    (by intro n m h; change 2*(p/2+n)+3=2*(p/2+m)+3 at h;omega)
  let C := 1+∑' n,W n
  have hC : 0<C := by
    have hh : 0≤∑' n,W n := tsum_nonneg hW
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro a η ha ε τ hε hεr hτ hτr δ hδ hcut
  let G := 1+|Real.log ε|
  have hG : 0≤G := by dsimp [G];positivity
  have hbound (n : ℕ) : wholeTransportedMass b B rcut j a η (p/2+n) ε τ≤ENNReal.ofReal (W n*G) := by
    have hex := full_shell_exponent_pos hp (high_odd_order_ge hp n) hj
    have hdeg : 2*j+3<(2*(p/2+n)+3)^2 := by omega
    exact hsource a η ha (p/2+n) hdeg ε τ hε hεr hτ hτr δ hδ hcut
  have hnorm (n : ℕ) : ‖wholeTransportedIntegral b B rcut j a η (p/2+n) ε τ‖≤W n*G := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound n)
    rw [ENNReal.toReal_ofReal (mul_nonneg (hW n) hG)] at hh
    exact (norm_integral_le_lintegral_norm _).trans hh
  have hnormsum := (hsum.mul_right G).of_nonneg_of_le (fun n => norm_nonneg _) hnorm
  have hCG : (∑' n,W n)*G≤C*G := mul_le_mul_of_nonneg_right (by dsimp [C];linarith) hG
  refine ⟨?_,hnormsum,?_⟩
  · calc
      _ ≤ ∑' n,ENNReal.ofReal (W n*G) := ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal ((∑' n,W n)*G) := by
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hW n) hG) (hsum.mul_right G),tsum_mul_right]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hCG
  · have hh := hnormsum.tsum_le_tsum hnorm (hsum.mul_right G)
    rw [tsum_mul_right] at hh
    exact hh.trans hCG

end
end IsingBulk.HT22.Far
