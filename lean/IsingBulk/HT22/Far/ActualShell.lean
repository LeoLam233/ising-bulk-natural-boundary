import IsingBulk.HT22.Far.ActualDensity
import IsingBulk.HT22.Far.ShellBudget
import IsingBulk.HT22.Geometry.SignedActualShell
import IsingBulk.Preferred22.ShellObligations

/-! The far estimate integrated on the actual signed eliminated-angle shell. -/
namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem actual_far_shell_lintegral (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ D C ε₀ τ₀ δB : ℝ, 0<D ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ d₀ : ℝ, 0<d₀ → ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
    ∀ a η : ℝ, ∀ m : ℕ, ∀ ε τ r : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → d₀≤r → ∀ l : ℤ,
    |b.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+r+ε≤M →
    ∀ i k : Fin (m+3),
    (∫⁻ x in signedRightShell a b B δB r l i k,
      ENNReal.ofReal ‖(2*Real.pi:ℂ)^(m+2)*transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal (farOrderEnvelope A L (m+3)*C*((m+3:ℕ):ℝ)*D^(m+1)*
        (r/Real.sqrt (|b.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+r+ε))^m*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hdensity⟩ := actual_far_density_bound b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨eF,tF,dF,heF,htF,hdF,hdFB,hdensity⟩ := hdensity B hB
  obtain ⟨D,C,eC,tC,dC,hD,hC,heC,htC,hdC,hdCB,hcoarea⟩ := signed_actual_shell_scale_lintegral b B
  let d := min dF dC
  refine ⟨D,C,min eF eC,min tF tC,d,hD,hC,lt_min heF heC,lt_min htF htC,
    lt_min hdF hdC,(min_le_left _ _).trans_lt hdFB,?_⟩
  intro d₀ hd₀ rcut hrcut hrper j
  obtain ⟨A,L,hA,hbound⟩ := hdensity d₀ hd₀ rcut hrcut hrper j
  refine ⟨A,L,hA,?_⟩
  intro a η m ε τ r hε hεr hτ hτr hr l hTM i k
  have henv : 0≤farOrderEnvelope A L (m+3) := by unfold farOrderEnvelope shellOrderEnvelope;positivity
  apply hcoarea a η m ε τ r d (farOrderEnvelope A L (m+3)) hε
    (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _))
    (hd₀.trans_le hr) (lt_min hdF hdC) (min_le_right _ _) henv l i k
    (fun w => ‖(2*Real.pi:ℂ)^(m+2)*transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε) w‖)
  intro x hx
  let w := constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x
  let μ := b.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)
  have hbox (q : Fin (m+3)) : -dF≤w q+b.b ∧ w q≤B.delta := by
    have hd : d≤dF := min_le_left _ _
    have hh := hx.1 q
    constructor <;> linarith [hh.1,hh.2]
  have hmean : (∑ q,(w q+b.b))=((m+3:ℕ):ℝ)*μ := by
    rw [Finset.sum_add_distrib]
    dsimp only [w,μ]
    rw [constrainedAtTotal_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : ((m+3:ℕ):ℝ)≠0 := by positivity
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
  simpa only [show m+3-1=m+2 by omega] using hbound η (m+3) (by omega) ε τ μ r hε
    (hεr.trans_le (min_le_left _ _)) hτ (hτr.trans_le (min_le_left _ _)) hr hTM
    w hbox hwin i k hx.2.1 hx.2.2.1

theorem actual_far_shell_envelope (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ d₀ : ℝ, 0<d₀ → ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
    ∀ a η : ℝ, ∀ m : ℕ, ∀ ε τ r : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → d₀≤r → ∀ l : ℤ,
    |b.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+r+ε≤M →
    ∀ i k : Fin (m+3),
    (∫⁻ x in signedRightShell a b B δB r l i k,
      ENNReal.ofReal ‖(2*Real.pi:ℂ)^(m+2)*transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal (farOrderEnvelope A L (m+3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hraw⟩ := actual_far_shell_lintegral b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨D,C,e,t,d,hD,hC,he,ht,hd,hdB,hraw⟩ := hraw B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro d₀ hd₀ rcut hrcut hrper j
  obtain ⟨A,L,hA,hraw⟩ := hraw d₀ hd₀ rcut hrcut hrper j
  refine ⟨A*(max 1 C)*(max 1 D)*(max 1 (Real.sqrt M)),L+1,by positivity,?_⟩
  intro a η m ε τ r hε hεr hτ hτr hr l hTM i k
  apply (hraw a η m ε τ r hε hεr hτ hτr hr l hTM i k).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (far_shell_envelope_absorption hA.le hC.le hD.le (hd₀.trans_le hr) hε.le hTM m L)
    (by positivity)

theorem actual_far_shell_envelope_shrinkable (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ d₀ : ℝ, 0<d₀ → ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
    ∀ a η : ℝ, ∀ m : ℕ, ∀ ε τ r : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → d₀≤r → ∀ l : ℤ,
    |b.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+r+ε≤M →
    ∀ δ : ℝ, δ≤δB → ∀ i k : Fin (m+3),
    (∫⁻ x in signedRightShell a b B δ r l i k,
      ENNReal.ofReal ‖(2*Real.pi:ℂ)^(m+2)*transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖) ≤
      ENNReal.ofReal (farOrderEnvelope A L (m+3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_far_shell_envelope b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro d₀ hd₀ rcut hrcut hrper j
  obtain ⟨A,L,hA,hsource⟩ := hsource d₀ hd₀ rcut hrcut hrper j
  refine ⟨A,L,hA,?_⟩
  intro a η m ε τ r hε hεr hτ hτr hr l hTM δ hδ i k
  apply le_trans ?_ (hsource a η m ε τ r hε hεr hτ hτr hr l hTM i k)
  apply lintegral_mono_set
  intro x hx
  refine ⟨hx.1,⟨?_,hx.2.1.2⟩,hx.2.2⟩
  intro q
  have hh := hx.2.1.1 q
  constructor <;> linarith [hh.1,hh.2]

end
end IsingBulk.HT22.Far
