import IsingBulk.HT22.Near.PhysicalDensity
import IsingBulk.HT22.Geometry.SignedActualShell
import IsingBulk.Preferred22.ShellObligations
import IsingBulk.HT22.Near.CoareaAbsorption

/-! The near estimate integrated on the actual signed eliminated-angle shell. -/
namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem actual_near_shell_lintegral (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ D C ε₀ τ₀ δB : ℝ, 0<D ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, 1≤A ∧
    ∀ a η : ℝ, ∀ n : ℕ, ∀ ε τ r : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → ∀ l : ℤ,
    |b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε≤M →
    ∀ i k : Fin (2*n+3),
    (∫⁻ x in signedRightShell a b B δB r l i k,
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal ((A^((2*n+3)^2)*(r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^((2*n+3)*(2*n+2))/(r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^(2*j))*C*((2*n+3:ℕ):ℝ)*D^(2*n+1)*
        (r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^(2*n)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hdensity⟩ := actual_near_physical_density b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨eF,tF,dF,heF,htF,hdF,hdFB,hdensity⟩ := hdensity B hB
  obtain ⟨D,C,eC,tC,dC,hD,hC,heC,htC,hdC,hdCB,hcoarea⟩ := signed_actual_shell_scale_lintegral b B
  let d := min dF dC
  refine ⟨D,C,min eF eC,min tF tC,d,hD,hC,lt_min heF heC,lt_min htF htC,
    lt_min hdF hdC,(min_le_left _ _).trans_lt hdFB,?_⟩
  intro rcut hrcut hrper j
  obtain ⟨A,hA,hbound⟩ := hdensity rcut hrcut hrper j
  refine ⟨A,hA,?_⟩
  intro a η n ε τ r hε hεr hτ hτr hr l hTM i k
  have hAn : 0≤A := le_trans (by norm_num) hA
  have henv : 0≤(A^((2*n+3)^2)*(r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^((2*n+3)*(2*n+2))/(r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^(2*j)) := by positivity
  apply hcoarea a η (2*n) ε τ r d ((A^((2*n+3)^2)*(r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^((2*n+3)*(2*n+2))/(r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^(2*j))) hε
    (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _))
    hr (lt_min hdF hdC) (min_le_right _ _) henv l i k
    (fun w => ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε) w‖)
  intro x hx
  let w := constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x
  let μ := b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)
  have hbox (q : Fin (2*n+3)) : -dF≤w q+b.b ∧ w q≤B.delta := by
    have hd : d≤dF := min_le_left _ _
    have hh := hx.1 q
    constructor <;> linarith [hh.1,hh.2]
  have hmean : (∑ q,(w q+b.b))=((2*n+3:ℕ):ℝ)*μ := by
    rw [Finset.sum_add_distrib]
    dsimp only [w,μ]
    rw [constrainedAtTotal_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : ((2*n+3:ℕ):ℝ)≠0 := by positivity
    field_simp
    ring
  have hwin : ∀ q, μ-2*r≤w q+b.b ∧ w q+b.b≤μ+2*r := by
    apply constrained_shell_coordinate_window (i := i) (j := k) (by omega) hmean
    · intro q
      have hh := hx.2.1 q
      constructor <;> linarith [hh.1,hh.2]
    · have hh := hx.2.2.2
      dsimp only [w]
      linarith
  simpa only [show 2*(n+1)+1=2*n+3 by omega,show 2*(n+1)=2*n+2 by omega,w,μ] using hbound η (n+1) ε τ μ r hε
    (hεr.trans_le (min_le_left _ _)) hτ (hτr.trans_le (min_le_left _ _)) hr hTM
    w hbox hwin i k hx.2.1 hx.2.2.1

/-- Exact integrated F001 exponent N²−2j−3. The coarea factor is the
actual signed full-occupancy one and all N-dependent costs are absorbed. -/
theorem actual_near_shell_quadratic (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ E : ℝ, 1≤E ∧ ∀ a η : ℝ, ∀ n : ℕ, ∀ ε τ r : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → ∀ l : ℤ,
    |b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε≤M → ∀ i k : Fin (2*n+3),
    (∫⁻ x in signedRightShell a b B δB r l i k,
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal (E^((2*n+3)^2)*
        (r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)|+r+ε))^
          (((2*n+3:ℕ):ℝ)^2-2*(j:ℝ)-3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hraw⟩ := actual_near_shell_lintegral b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨D,C,e,t,δ,hD,hC,he,ht,hδ,hδB,hraw⟩ := hraw B hB
  refine ⟨e,t,δ,he,ht,hδ,hδB,?_⟩
  intro rcut hrcut hperiod j
  obtain ⟨A,hA,hraw⟩ := hraw rcut hrcut hperiod j
  obtain ⟨E,hE,habs⟩ := coarea_quadratic_absorption
    (le_trans (by norm_num) hA) hC.le hD.le
  refine ⟨E,hE,?_⟩
  intro a η n ε τ r hε hεr hτ hτr hr l hTM i k
  apply (hraw a η n ε τ r hε hεr hτ hτr hr l hTM i k).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (habs (2*n) j _ (by positivity)) (by positivity)

end
end IsingBulk.HT22.Near
