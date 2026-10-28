import IsingBulk.HT22.SmallTube.Cover
import IsingBulk.HT22.SmallTube.Radius
namespace IsingBulk.HT22.SmallTube
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry IsingBulk.HT22.Near
open scoped Topology ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

def labelCount (n : ℕ) : ℝ := ((preferredMeanIndices (2*n+3)).card:ℝ)*(2*n+3)*(2*n+3)

theorem smallMass_bound_of_near (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (δ : ℝ) (hδ : δ < B.delta) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData b B δ rcut) (j : ℕ) (a η : ℝ)
    (ha : |a| ≤ Real.pi) (n : ℕ) (ε τ R D : ℝ) (hε : 0 ≤ ε)
    (hnear : ∀ l : ℤ, ∀ i k : Fin (2*n+3),
      nearPhysicalShellSum b B δ (Real.sqrt R) rcut j a η n ε τ l i k ≤ ENNReal.ofReal D) :
    (∫⁻ x : Fin (2*n+2) → ℝ in angularBox (2*n+2),
      smallMassIntegrand a (Complex.exp (-Complex.I*(η:ℂ))) b B τ rcut j
        (IsingBulk.Branch.radialParameter b.alpha ε) R x) ≤ ENNReal.ofReal (labelCount n * D) := by
  apply (smallMass_le_near_sum b B δ hδ rcut hcut j a η ha n ε τ R hε).trans
  calc
    _ ≤ ∑ _l : {l : ℤ // l∈preferredMeanIndices (2*n+3)},
        ∑ _i : Fin (2*n+3), ∑ _k : Fin (2*n+3), ENNReal.ofReal D := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact hnear l.1 i k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      unfold labelCount
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast]
      have hN : ENNReal.ofReal (2*(n:ℝ)+3)=((2*n+3:ℕ):ℝ≥0∞) := by
        norm_cast
      rw [hN]
      ring

/-- Genuine physical small-tube mass, including the original full angular
measure, signed constraint and all actual transported density factors. -/
theorem actual_small_tube_mass (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ δ : ℝ, δ≤δB → ∀ rcut : ℝ → ℝ, PreferredRightCutoffData b B δ rcut →
    ∀ j n : ℕ, 6≤(2*n+3)^2-2*j-3 → ∃ K : ℝ, 0<K ∧
    ∀ a η ε τ : ℝ, |a|≤Real.pi → 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ m : ℕ,
    (∫⁻ x : Fin (2*n+2) → ℝ in angularBox (2*n+2),
      smallMassIntegrand a (Complex.exp (-Complex.I*(η:ℂ))) b B τ rcut j
        (IsingBulk.Branch.radialParameter b.alpha ε) (preferredDyadicRadius m) x) ≤
      ENNReal.ofReal (K*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_near_dyadic_mass b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro δ hδ rcut hcut j n hq
  obtain ⟨E,hE,hsource⟩ := hsource rcut hcut.2.2.1 hcut.2.2.2.1 j
  let q := (2*n+3)^2-2*j-3
  let L := labelCount n
  let A := Real.pi^3 * (max 1 (Real.sqrt Real.pi))^q
  let K := (L+1)*4*E^((2*n+3)^2)*A
  have hL : 0≤L := by dsimp [L,labelCount]; positivity
  have hEn : 0≤E := le_trans (by norm_num) hE
  have hA : 0<A := by dsimp [A]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro a η ε τ ha hε hεr hτ hτr m
  apply (smallMass_bound_of_near b B δ (hδ.trans_lt hdB) rcut hcut j a η ha n ε τ
    (preferredDyadicRadius m) _ hε.le
    (hsource a η n (by omega) ε τ δ (Real.sqrt (preferredDyadicRadius m))
      hε hεr hτ hτr hδ (Real.sqrt_nonneg _))).trans
  apply ENNReal.ofReal_le_ofReal
  have hr := dyadic_sqrt_power_le hq m
  have hlog : 0≤1+|Real.log ε| := by positivity
  calc
    _ ≤ L*(4*E^((2*n+3)^2)*(A*(1/8:ℝ)^m)*(1+|Real.log ε|)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr (by positivity)) hlog) hL
    _ ≤ K*(1+|Real.log ε|)*(1/8:ℝ)^m := by
      dsimp [K]
      nlinarith [mul_nonneg (show 0≤4*E^((2*n+3)^2)*A*(1+|Real.log ε|)*(1/8:ℝ)^m by positivity) (show 0≤(1:ℝ) by norm_num)]
end
end IsingBulk.HT22.SmallTube
