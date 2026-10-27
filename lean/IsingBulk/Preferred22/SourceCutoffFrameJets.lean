import IsingBulk.Preferred22.SeparatedJetBounds

/-! Actual complete real cutoff frame bounds on the full right source.
The parameter and contour thresholds precede all jet orders and particle
numbers. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

private theorem preferred_matrix_entry_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (f : E → Matrix (Fin N) (Fin N) ℂ) (hf : ContDiff ℝ ∞ f)
    (x : E) (j : ℕ) (i b : Fin N) :
    ‖iteratedFDeriv ℝ j (fun y => f y i b) x‖≤‖iteratedFDeriv ℝ j f x‖ := by
  let L : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj b : (Fin N → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj i : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → ℂ))
  have hL : ‖L‖≤1 := by
    apply L.opNorm_le_bound zero_le_one
    intro A
    change ‖A i b‖≤1*‖A‖
    simpa only [one_mul] using (norm_le_pi_norm (A i) b).trans (norm_le_pi_norm A i)
  exact (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp : (j:ℕ∞ω)≤∞)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hL)

/-- The open frame chart used by the finite expansion is constructed from
actual strict physical margins; no chart hypothesis remains here. -/
theorem preferredFrameJet_angular_norm_at {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hM : ∀ θ : Fin N → ℝ, (preferredContourMatrix τ p m θ).det≠0)
    (G : (Fin N → ℝ) → ℂ) (hG : ContDiff ℝ ∞ G)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (J : ℕ) {A U M : ℝ} (hA : 0≤A) (hU1 : 1≤U) (hM1 : 1≤M)
    (hGjet : ∀ k≤J, ‖iteratedFDeriv ℝ k G θ‖≤A)
    (hUjet : ∀ a b, ∀ k≤J, ‖iteratedFDeriv ℂ k
      (preferredSeparatedInverseFactor (N:=N) a b) (s,preferredSourceCoordinate τ p m s θ)‖≤U)
    (hMjet : ∀ i b, ∀ k≤J,
      ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹ i b) θ‖≤M*(N:ℝ)^J)
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) :
    ‖preferredFrameJet τ p m (fun _ x => G x) xs s θ‖≤
      (2*((2^J*U)*(2^J*M)))^J*(N:ℝ)^(J*J+2*J)*A := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp hgeom
  exact preferredFrameJet_angular_norm_on_chart hN τ δ p m hp hm hM Ω hΩ
    (fun z hz => hΩsub hz) G hG s θ hz J hA hU1 hM1 hGjet hUjet hMjet xs hxs

/-- Uniform source geometry and quantitative real-factor frame control.
The finite initial angular jets are explicit; the true inverse matrix and
all inverse-chart multiplier bounds are discharged on the actual source. -/
theorem preferred_actual_angular_frame_control (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ J : ℕ, ∃ C : ℝ, 1≤C ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      (∀ x : Fin N → ℝ, (preferredContourMatrix τ B.p B.m x).det≠0) ∧
      ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹) ∧
      (∀ i b, ∀ k≤J,
        ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹ i b) θ‖≤C*(N:ℝ)^J) ∧
      (∀ xs : List (Option (Fin N)), xs.length≤J → ∀ i,
        ‖preferredFrameJet τ B.p B.m
          (fun t x => preferredSourceUQ t (preferredSourceCoordinate τ B.p B.m t x i)) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C ∧
        ‖preferredFrameJet τ B.p B.m
          (fun t x => preferredSourceUDot t (preferredSourceCoordinate τ B.p B.m t x i)) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C) ∧
      ∀ G : (Fin N → ℝ) → ℂ, ContDiff ℝ ∞ G → ∀ A : ℝ, 0≤A →
      (∀ k≤J, ‖iteratedFDeriv ℝ k G θ‖≤A) →
      ∀ xs : List (Option (Fin N)), xs.length≤J →
      ‖preferredFrameJet τ B.p B.m (fun _ x => G x) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ)^(J*J+2*J)*A := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨δ,εf,τf,hδ,hδa,hεf,hτf,hframe⟩ := preferred_actual_frame_points d B
  obtain ⟨τI,hτI,hIjet⟩ := preferredContourMatrix_inverse_uniform_angular_jets B.p B.m B.smooth B.m_smooth
    B.periodic hmp
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound _)]; exact B.upper_bound _)
  obtain ⟨τM,hτM,hM⟩ := preferred_bump_matrix_uniform d B
  let ε₀ := min r (min (ρ/2) εf)
  let τ₀ := min r (min τf (min τI τM))
  let δB := min (B.delta/2) (r/2)
  have hδB : 0<δB := lt_min (half_pos B.delta_pos) (half_pos hr)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt (by linarith [B.delta_pos])
  refine ⟨ε₀,τ₀,δB,lt_min hr (lt_min (half_pos hρ) hεf),
    lt_min hr (lt_min hτf (lt_min hτI hτM)),hδB,hδBB,?_⟩
  intro J
  obtain ⟨U,hU1,hUjet⟩ := preferred_inverse_domain_finite_jets d ρ D hρ hDc
    (fun s q hs hq => (hgood s q q hs hq hq).2.1) J
  choose I hI hIj using hIjet
  let M := 1+∑ k∈Finset.range (J+1), I k
  have hsumI : 0≤∑ k∈Finset.range (J+1), I k := Finset.sum_nonneg (fun k _ => (hI k).le)
  have hM1 : 1≤M := by dsimp [M]; linarith
  have hIM (k : ℕ) (hk : k≤J) : I k≤M := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.range (J+1)) => (hI l).le)
      (show k∈Finset.range (J+1) by simp; omega)
    dsimp [M]
    linarith
  let K := (2*((2^J*U)*(2^J*M)))^J
  have hK : 1≤K := by
    apply one_le_pow₀
    have htwo : (1:ℝ)≤2^J := one_le_pow₀ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le (by norm_num)
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le htwo hU1)
        (one_le_mul_of_one_le_of_one_le htwo hM1))
  let C := max U (max K M)
  have hC : 1≤C := hU1.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hepsr : ε<r := hεr.trans_le (min_le_left _ _)
  have hepsρ : ε<ρ/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsf : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ht : τ<r := hτr.trans_le (min_le_left _ _)
  have htf : τ<τf := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htI : τ<τI := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htM : τ<τM := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hs : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hepsρ.le
  have hq (i : Fin N) : preferredSourceCoordinate τ B.p B.m s θ i∈D := by
    apply interior_subset
    have hpocc := preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ
    have hmocc := preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hepsr)
      (by simpa only [abs_of_nonneg hτ] using ht) hpocc hmocc
      (by have hh := (hθ i).1; have hd : δB≤r/2 := min_le_right _ _; linarith)
      (by have hh := (hθ i).2; linarith)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hepsf hτ htf θ hθ
  have hMall : ∀ x : Fin N → ℝ, (preferredContourMatrix τ B.p B.m x).det≠0 := hM N hN τ hτ htM
  have hInv : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹) :=
    contDiff_iff_contDiffAt.mpr (fun x => preferredContourMatrix_inverse_contDiffAt τ B.p B.m
      B.smooth B.m_smooth x (hMall x))
  have hMj (i b : Fin N) (k : ℕ) (hk : k≤J) :
      ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹ i b) θ‖≤M*(N:ℝ)^J := by
    exact (preferred_matrix_entry_jet_le _ hInv θ k i b).trans
      ((hIj k τ hτ htI.le N hN θ).trans
        (mul_le_mul (hIM k hk) (pow_le_pow_right₀ hn hk) (by positivity) (zero_le_one.trans hM1)))
  have hUj (a : Option (Fin N)) (b : Fin N) (k : ℕ) (hk : k≤J) :
      ‖iteratedFDeriv ℂ k (preferredSeparatedInverseFactor a b) (s,preferredSourceCoordinate τ B.p B.m s θ)‖≤U :=
    preferredSeparatedInverseFactor_jet_le a b _ k (zero_le_one.trans hU1) hpoint.inverse_analytic
      (fun i => hUjet s _ hs (hq i) k hk)
  refine ⟨hMall,hInv,?_,?_,?_⟩
  · intro i b k hk
    exact (hMj i b k hk).trans (mul_le_mul_of_nonneg_right
      ((le_max_right K M).trans (le_max_right U _)) (by positivity))
  · intro xs hxs i
    have hUqs := preferredSourceUQ_analyticAt_of_joint s _ (hpoint.inverse_analytic i)
    have hUss := preferredSourceUDot_analyticAt_of_joint s _ (hpoint.inverse_analytic i)
    constructor
    · exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth
        s θ hpoint hθstrict (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2)
        (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) (preferredOneProjection i)
        (preferredOneProjection_norm_le i) hUqs Filter.EventuallyEq.rfl xs C (zero_le_one.trans hC)
        (((hUjet s _ hs (hq i) xs.length hxs).1).trans (le_max_left _ _))
    · exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth
        s θ hpoint hθstrict (fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2)
        (fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2) (preferredOneProjection i)
        (preferredOneProjection_norm_le i) hUss Filter.EventuallyEq.rfl xs C (zero_le_one.trans hC)
        (((hUjet s _ hs (hq i) xs.length hxs).2).trans (le_max_left _ _))
  · intro G hG A hA hGj xs hxs
    have hh := preferredFrameJet_angular_norm_at hN τ δ B.p B.m B.smooth B.m_smooth hMall G hG
      s θ hpoint hθstrict J hA hU1 hM1 hGj hUj hMj xs hxs
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((le_max_left K M).trans (le_max_right U _)) (by positivity)) hA)

/-- Every literal frame word of the complete right cell weight has the
allowed exponential-times-polynomial particle-number bound. Both true
occupancies and the whole smooth real telescope remain in the statement. -/
theorem preferred_actual_cell_weight_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ J : ℕ, ∃ C : ℝ, 1≤C ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      ∀ xs : List (Option (Fin N)), xs.length≤J →
      ‖preferredFrameJet τ B.p B.m
        (fun _ x => (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut x:ℂ)) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C^N*(N:ℝ)^(J*J+5*J) := by
  obtain ⟨cap,hcap,hcapa,hcontrol⟩ := preferred_actual_angular_frame_control d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,hjet⟩ := hcontrol B hBcap
  refine ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro rcut hrcut hrper J
  obtain ⟨K,hK,hframe⟩ := hjet J
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  obtain ⟨W,hW,hWjet⟩ := preferredCellWeight_right_finite_jets B.p B.m rcut B.smooth B.m_smooth hrcut
    B.periodic hmp hrper J
  refine ⟨K*W,one_le_mul_of_one_le_of_one_le hK hW,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs
  let G := fun x : Fin N → ℝ => (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut x:ℂ)
  have hreal : ContDiff ℝ ∞ (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut : (Fin N → ℝ) → ℝ) := by
    have hη := preferredPopulationCutoff_smooth
    have hp := B.smooth
    have hm := B.m_smooth
    unfold preferredCellWeight preferredLowerWeight lowerWeight preferredRightWeight occupancy
    fun_prop
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hreal
  have hGj (k : ℕ) (hk : k≤J) : ‖iteratedFDeriv ℝ k G θ‖≤W^N*(N:ℝ)^(3*J) :=
    ofReal_jet_le _ hreal θ k (hWjet N hN θ k hk)
  have hh := (hframe N hN ε τ hε hεr hτ hτr θ hθ).2.2.2.2 G hG
    (W^N*(N:ℝ)^(3*J)) (by positivity) hGj xs hxs
  apply hh.trans
  calc
    _ = K*W^N*(N:ℝ)^(J*J+5*J) := by
      rw [show J*J+5*J=(J*J+2*J)+3*J by omega,pow_add]
      ring
    _ ≤ K^N*W^N*(N:ℝ)^(J*J+5*J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hK (by omega : N≠0)) (by positivity)
    _ = (K*W)^N*(N:ℝ)^(J*J+5*J) := by rw [mul_pow]

/-- Actual inverse occupancy matrix entries have uniformly polynomial
bounds under every literal source-frame word. -/
theorem preferred_actual_matrix_inverse_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ J : ℕ, ∃ C : ℝ, 1≤C ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      ∀ xs : List (Option (Fin N)), xs.length≤J → ∀ i b,
      ‖preferredFrameJet τ B.p B.m
        (fun _ x => (preferredContourMatrix τ B.p B.m x)⁻¹ i b) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ)^(J*J+3*J) := by
  obtain ⟨cap,hcap,hcapa,hcontrol⟩ := preferred_actual_angular_frame_control d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,hjet⟩ := hcontrol B hBcap
  refine ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro J
  obtain ⟨K,hK,hframe⟩ := hjet J
  refine ⟨K^2,one_le_pow₀ hK,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs i b
  obtain ⟨_,hM,hMj,_,hG⟩ := hframe N hN ε τ hε hεr hτ hτr θ hθ
  have hentry : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹ i b) :=
    contDiff_pi.mp (contDiff_pi.mp hM i) b
  have hh := hG _ hentry (K*(N:ℝ)^J) (by positivity) (hMj i b) xs hxs
  apply hh.trans_eq
  rw [show J*J+3*J=(J*J+2*J)+J by omega,pow_add]
  ring

end
end IsingBulk.Preferred22
