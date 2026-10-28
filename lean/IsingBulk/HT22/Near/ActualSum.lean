import IsingBulk.HT22.Near.ActualDyadicSum
import IsingBulk.HT22.Near.LabelSum

namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Geometry Set MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Complete near dyadic/mean/extrema sum. The single threshold is fixed
before particle number and epsilon, and the full N² suppression is retained. -/
theorem actual_near_shell_sum (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ δ₀ H : ℝ, 0<δ₀ ∧ δ₀≤1 ∧ 0<H ∧
    ∀ a η : ℝ, ∀ n : ℕ, 2*j+3<(2*n+3)^2 → ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ δ : ℝ, δ≤δB →
    (∑' q : ℕ, ∑ l : {l : ℤ // l∈preferredMeanIndices (2*n+3)},
      ∑ i : Fin (2*n+3),∑ k : Fin (2*n+3),
      if dyadicScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((2*n+3:ℕ):ℝ)) ε q≤δ₀ then
        physicalShellMass b B δ rcut j a η n ε τ q l.1 i k else 0)≤
      ENNReal.ofReal (H*nearOrderEnvelope (2*n+3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hraw⟩ := actual_near_dyadic_mass b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hraw⟩ := hraw B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro rcut hrcut hperiod j
  obtain ⟨E,hE,hraw⟩ := hraw rcut hrcut hperiod j
  obtain ⟨F,hF,hcount⟩ := near_label_quadratic_absorb hE
  let δ₀ := 1/(2*F)
  have hF0 : 0<F := lt_of_lt_of_le zero_lt_one hF
  have hδ₀ : 0<δ₀ := by dsimp [δ₀];positivity
  have hδ₀1 : δ₀≤1 := by dsimp [δ₀];apply (div_le_one₀ (by positivity)).mpr;linarith
  have hsmall : F*δ₀≤1/2 := by dsimp [δ₀];field_simp;norm_num
  refine ⟨δ₀,4*δ₀^(-2*(j:ℝ)-3),hδ₀,hδ₀1,by positivity,?_⟩
  intro a η n hdeg ε τ hε hεr hτ hτr δ hδ
  let N := 2*n+3
  let P := N^2-2*j-3
  let G := 1+|Real.log ε|
  have hG : 0≤G := by dsimp [G];positivity
  let f : ℕ → {l : ℤ // l∈preferredMeanIndices N} → Fin N → Fin N → ℝ≥0∞ :=
    fun q l i k => if dyadicScale (b.b+(a+2*Real.pi*(l.1:ℝ))/(N:ℝ)) ε q≤δ₀ then
      physicalShellMass b B δ rcut j a η n ε τ q l.1 i k else 0
  have hb (l) (i k : Fin N) : (∑' q,f q l i k)≤ENNReal.ofReal (4*E^(N^2)*δ₀^P*G) :=
    hraw a η n hdeg ε τ δ δ₀ hε hεr hτ hτr hδ hδ₀.le l.1 i k
  have hh := infinite_shell_label_sum_bound (show 0<N by dsimp [N];omega) f
    (ENNReal.ofReal (4*E^(N^2)*δ₀^P*G)) hb
  change (∑' q,∑ l,∑ i,∑ k,f q l i k)≤_
  apply hh.trans
  rw [←ENNReal.ofReal_natCast (3*N^3),←ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hcoeff := hcount N (by dsimp [N];omega)
  have hth := near_shell_threshold_bound hF0.le hδ₀ hδ₀1 hsmall (le_refl j) N
  have hpdeg := (natural_collision_degree hdeg).2
  change (P:ℝ)=(N:ℝ)^2-2*(j:ℝ)-3 at hpdeg
  rw [←hpdeg,Real.rpow_natCast] at hth
  calc
    _ = 4*((3*(N:ℝ)^3)*E^(N^2))*δ₀^P*G := by push_cast;ring
    _ ≤ 4*F^(N^2)*δ₀^P*G := by gcongr
    _ = 4*(F^(N^2)*δ₀^P)*G := by ring
    _ ≤ 4*(δ₀^(-2*(j:ℝ)-3)*nearOrderEnvelope N)*G := by gcongr
    _ = _ := by ring

end
end IsingBulk.HT22.Near
