import IsingBulk.HT22.Near.UniformShell
import IsingBulk.HT22.Near.ENNRealDyadic

namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Geometry Set MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

def physicalShellMass (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (δB : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (a η : ℝ) (n : ℕ) (ε τ : ℝ)
    (m : ℕ) (l : ℤ) (i k : Fin (2*n+3)) : ℝ≥0∞ :=
  ∫⁻ x in signedRightShell a b B δB (preferredDyadicRadius m) l i k,
    ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖

def nearPhysicalShellSum (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (δB δ₀ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (a η : ℝ) (n : ℕ) (ε τ : ℝ)
    (l : ℤ) (i k : Fin (2*n+3)) : ℝ≥0∞ :=
  ∑' m,if dyadicScale (b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)) ε m≤δ₀
    then physicalShellMass b B δB rcut j a η n ε τ m l i k else 0

theorem natural_collision_degree {N j : ℕ} (h : 2*j+3<N^2) :
    1≤N^2-2*j-3 ∧ ((N^2-2*j-3:ℕ):ℝ)=(N:ℝ)^2-2*(j:ℝ)-3 := by
  constructor
  · omega
  · rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_pow,Nat.cast_mul]
    norm_num

theorem actual_near_dyadic_mass (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ E : ℝ, 1≤E ∧ ∀ a η : ℝ, ∀ n : ℕ,
    2*j+3<(2*n+3)^2 → ∀ ε τ δ δ₀ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → δ≤δB → 0≤δ₀ →
    ∀ l : ℤ, ∀ i k : Fin (2*n+3),
    nearPhysicalShellSum b B δ δ₀ rcut j a η n ε τ l i k ≤
      ENNReal.ofReal (4*E^((2*n+3)^2)*δ₀^((2*n+3)^2-2*j-3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_near_dyadic_shell b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro rcut hrcut hperiod j
  obtain ⟨E,hE,hsource⟩ := hsource rcut hrcut hperiod j
  refine ⟨E,hE,?_⟩
  intro a η n hdeg ε τ δ δ₀ hε hεr hτ hτr hδ hδ₀ l i k
  obtain ⟨hp,hpdegree⟩ := natural_collision_degree hdeg
  apply near_raw_dyadic_ennreal_sum _ hε.le hδ₀
    (pow_nonneg (le_trans (by norm_num) hE) _) (by positivity) hp
  intro m _hm
  have hh := hsource a η n m ε τ δ hε hεr hτ hτr hδ l i k
  rw [←hpdegree,Real.rpow_natCast] at hh
  exact hh

end
end IsingBulk.HT22.Near
