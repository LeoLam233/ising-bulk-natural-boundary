import IsingBulk.HT22.Transport.FieldNeighborhood.AngularFrameBound
import IsingBulk.HT22.Transport.FieldNeighborhood.UniformFrameBudget
import IsingBulk.HT22.Tail.ActualCollisionChart
import IsingBulk.HT22.Transport.InverseFactorJets.Actual

/-! Full actual F001 fixed-v angular V word jets, with the original real
occupancy matrix and total parameter-plus-coordinate loss. The source regime
precedes every derivative order and particle number. -/
namespace IsingBulk.HT22
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem actual_angular_field_uniform_frame_budget (b : PreferredBranchData)
    (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧
      ∀ B : PreferredCoareaBump b, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ a : Fin N,
      ‖frameJet τ B.p B.m (fun t x => angularField τ B.p B.m t x a)
        xs (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤
        C*(N:ℝ)^(2*(j*j+4*j)+(2*j+2)+1)/(r/Real.sqrt (|μ|+r+ε))^(1+xs.length) := by
  obtain ⟨capC,hcapC,hcapCa,hchart⟩ := actual_collision_source_chart b
  obtain ⟨capF,hcapF,_hcapFa,hfactor⟩ := InverseFactorJets.actual_inverse_factor_frame_jets b
  obtain ⟨capB,hcapB,_hcapBa,hfield⟩ := actual_mixed_field_uniform_frame_budget_uniform_cap b M hM
  refine ⟨min capC (min capF capB),lt_min hcapC (lt_min hcapF hcapB),
    (min_le_left _ _).trans_lt hcapCa,?_⟩
  intro B hBcap
  have hBF : B.delta<capF := hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hBB : B.delta<capB := hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c,δ,eC,tC,dC,_hc,heC,htC,hdC,hdCB,hchart⟩ := hchart B
    (hBcap.trans_le (min_le_left _ _))
  obtain ⟨eF,tF,dF,heF,htF,hdF,hdFB,hfactor⟩ := hfactor B hBF
  obtain ⟨eB,tB,dB,heB,htB,hdB,hdBB,hfield⟩ := hfield B
  let e := min eC (min eF eB)
  let t := min tC (min tF tB)
  let d := min dC (min dF dB)
  refine ⟨e,t,d,lt_min heC (lt_min heF heB),lt_min htC (lt_min htF htB),
    lt_min hdC (lt_min hdF hdB),(min_le_left _ _).trans_lt hdCB,?_⟩
  intro j
  obtain ⟨A,hA,hfactor⟩ := hfactor j
  obtain ⟨R,hR,hfield⟩ := hfield j
  let D := max 1 (Real.sqrt M)
  let C := (2:ℝ)^j*A^2*D^(j+1)+((2:ℝ)^j*A*D^j)*((2:ℝ)^j*A*D^j*R)
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hD : 1≤D := le_max_left _ _
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N hN ε τ μ r hε he hτ ht hr hTM θ hθ hwin i k hext hgap xs hxs a
  have hes : ε<eC ∧ ε<eF ∧ ε<eB := by simpa only [e,lt_min_iff] using he
  have hts : τ<tC ∧ τ<tF ∧ τ<tB := by simpa only [t,lt_min_iff] using ht
  have hds : d≤dC ∧ d≤dF ∧ d≤dB :=
    ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hbox (d' : ℝ) (hd' : d≤d') (a : Fin N) :
      -d'≤θ a+b.b ∧ θ a+b.b≤b.b+B.delta := by
    constructor <;> linarith [(hθ a).1,(hθ a).2]
  have hboxB (a : Fin N) : -dB≤θ a+b.b ∧ θ a≤min capB B.delta :=
    ⟨by linarith [(hθ a).1,hds.2.2],le_min ((hθ a).2.trans hBB.le) (hθ a).2⟩
  obtain ⟨Ω,hΩ,hz,hpoint,hRcov,_⟩ := hchart N hN ε τ μ r hε hes.1 hτ hts.1 hr
    θ (hbox dC hds.1) hwin i k hext hgap
  obtain ⟨hMm,hQm,hDm,hBm⟩ := source_generator_factors_mixed τ δ B.p B.m B.smooth B.m_smooth
    Ω hpoint hRcov
  have hT : 0< |μ|+r+ε := by positivity
  have hs : 0<Real.sqrt (|μ|+r+ε) := Real.sqrt_pos.mpr hT
  have hscale : r/Real.sqrt (|μ|+r+ε)≤D := by
    calc
      _ ≤ Real.sqrt (|μ|+r+ε) := (div_le_iff₀ hs).mpr (by
        rw [Real.mul_self_sqrt hT.le]; linarith [abs_nonneg μ])
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hTM
      _ ≤ D := le_max_right _ _
  exact angularField_frame_polynomial_bound hN τ δ B.p B.m B.smooth B.m_smooth
    Ω hΩ hpoint hRcov hMm hQm hDm hBm _ θ hz (r/Real.sqrt (|μ|+r+ε))
    j (j*j+4*j) (2*j+2) A R D hAp.le hR.le (by positivity) hscale hD
    (fun i a ys hys => (hfactor N hN ε τ hε hes.2.1 hτ hts.2.1 θ
      (hbox dF hds.2.1) ys hys).1 i a)
    (fun a ys hys => (hfactor N hN ε τ hε hes.2.1 hτ hts.2.1 θ
      (hbox dF hds.2.1) ys hys).2 a)
    (fun a ys hys => hfield N hN ε τ μ r hε hes.2.2 hτ hts.2.2 hr hTM θ hboxB
      hwin i k hext hgap ys hys a) xs hxs a

/-- A pointwise flux-ready consequence genuinely consuming the all-order V
producer. The extra particle power is harmless for fixed-N puncture limits. -/
theorem actual_angular_field_shell_bound_from_jets (b : PreferredBranchData)
    (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧
      ∀ B : PreferredCoareaBump b, B.delta<cap →
      ∃ C ε₀ τ₀ δB : ℝ, 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ a : Fin N, ‖angularField τ B.p B.m
        (IsingBulk.Branch.radialParameter b.alpha ε) θ a‖≤C*(N:ℝ)^3/r := by
  obtain ⟨cap,hcap,hcapa,h⟩ := actual_angular_field_uniform_frame_budget b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,h⟩ := h B hB
  obtain ⟨C,hC,h⟩ := h 0
  refine ⟨C*Real.sqrt M,e,t,d,mul_pos hC (Real.sqrt_pos.mpr hM),he,ht,hd,hdB,?_⟩
  intro N hN ε τ μ r hε her hτ htr hr hTM θ hθ hwin i k hext hgap a
  have hh := h N hN ε τ μ r hε her hτ htr hr hTM θ hθ hwin i k hext hgap [] (by simp) a
  simp only [frameJet,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.add_zero,pow_one] at hh
  apply hh.trans
  have hT : 0< |μ|+r+ε := by positivity
  have hs : Real.sqrt (|μ|+r+ε)≠0 := (Real.sqrt_pos.mpr hT).ne'
  calc
    _ = C*(N:ℝ)^3*Real.sqrt (|μ|+r+ε)/r := by field_simp
    _ ≤ C*(N:ℝ)^3*Real.sqrt M/r := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTM) (by positivity)) hr.le
    _ = _ := by ring

/-- Whole actual right rectangle, no shell/mean/extrema premise. This is the
flux consumer of the all-order V family, with all thresholds still before N. -/
theorem actual_angular_field_diameter_bound_from_jets (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧
      ∀ B : PreferredCoareaBump b, B.delta<cap →
      ∃ C ε₀ τ₀ δB : ℝ, 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta) →
      0<preferredAngularDiameter θ →
      ∀ a : Fin N, ‖angularField τ B.p B.m
        (IsingBulk.Branch.radialParameter b.alpha ε) θ a‖≤
          C*(N:ℝ)^3/preferredAngularDiameter θ := by
  classical
  let M := 5*Real.pi+1
  obtain ⟨cap,hcap,hcapa,h⟩ := actual_angular_field_shell_bound_from_jets b M (by dsimp [M]; positivity)
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨C,e,t,d,hC,he,ht,hd,hdB,h⟩ := h B hB
  refine ⟨C,min e 1,t,d,hC,lt_min he zero_lt_one,ht,hd,hdB,?_⟩
  intro N hN ε τ hε her hτ htr θ hθ hdiam a
  have hnon : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ θ hnon
  obtain ⟨k,_,hmax⟩ := Finset.exists_max_image Finset.univ θ hnon
  have hext (a : Fin N) : θ i≤θ a ∧ θ a≤θ k :=
    ⟨hmin a (Finset.mem_univ _),hmax a (Finset.mem_univ _)⟩
  let r := θ k-θ i
  let μ := θ i+b.b
  have hdiamr : preferredAngularDiameter θ≤r := by
    apply Metric.diam_le_of_forall_dist_le (show 0≤r by dsimp [r];linarith [(hext k).1])
    rintro _ ⟨a,rfl⟩ _ ⟨v,rfl⟩
    rw [Real.dist_eq,abs_le]
    constructor <;> dsimp [r] <;> linarith [(hext a).1,(hext a).2,(hext v).1,(hext v).2]
  have hr : 0<r := hdiam.trans_le hdiamr
  have hμ : |μ|≤2*Real.pi := by
    apply abs_le.mpr
    dsimp [μ]
    constructor <;> linarith [(hθ i).1,(hθ i).2,B.delta_alpha,b.alpha_lt,b.b_lt,Real.pi_pos]
  have hrpi : r≤2*Real.pi := by
    dsimp [r]
    linarith [(hθ i).1,(hθ k).2,B.delta_alpha,b.alpha_lt,b.b_lt]
  have hTM : |μ|+r+ε≤M := by
    have he1 := her.trans_le (min_le_right _ _)
    dsimp [M]
    linarith [Real.pi_pos]
  have hwindow (a : Fin N) : μ-2*r≤θ a+b.b ∧ θ a+b.b≤μ+2*r := by
    dsimp [μ,r]
    constructor <;> linarith [(hext a).1,(hext a).2,(hext k).1]
  have hbox (a : Fin N) : -d≤θ a+b.b ∧ θ a≤B.delta :=
    ⟨(hθ a).1,by linarith [(hθ a).2]⟩
  exact (h N hN ε τ μ r hε (her.trans_le (min_le_left _ _)) hτ htr hr hTM
    θ hbox hwindow i k hext le_rfl a).trans
      (div_le_div_of_nonneg_left (by positivity) hdiam hdiamr)

end
end IsingBulk.HT22
