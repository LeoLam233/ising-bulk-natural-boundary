import IsingBulk.Preferred22.AnchorScalarJets
import IsingBulk.Preferred22.AnchorCutoffJets
import IsingBulk.Preferred22.SourceCutoffFrameJets

/-! Whole one-sided source control of real angular cutoff factors in the
actual fixed-q frames. These estimates do not require a collision margin. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem preferred_anchor_matrix_entry_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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


/-- The actual whole-contour frame bounds for an arbitrary smooth angular
factor, with its finite angular jets kept explicit. -/
theorem preferred_actual_whole_angular_frame_control (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ G : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ G → ∀ A : ℝ,0≤A →
      (∀ k≤J,‖iteratedFDeriv ℝ k G θ‖≤A) →
      ∀ xs : List (Option (Fin N)),xs.length≤J →
      ‖preferredFrameJet τ B.p B.m (fun _ x => G x) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ)^(J*J+2*J)*A := by
  obtain ⟨cap,hcap,hcapa,hscalar⟩ := preferred_actual_anchor_scalar_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨εa,τa,_q₀,hεa,hτa,_hq₀,_hq₀1,hscalar'⟩ := hscalar B hBcap 1 zero_lt_one
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  obtain ⟨τI,hτI,hIjet⟩ := preferredContourMatrix_inverse_uniform_angular_jets B.p B.m B.smooth B.m_smooth
    B.periodic hmp
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound _)]; exact B.upper_bound _)
  obtain ⟨τM,hτM,hM⟩ := preferred_bump_matrix_uniform d B
  let ε₀ := min εa εf
  let τ₀ := min τa (min τf (min τI τM))
  refine ⟨ε₀,τ₀,lt_min hεa hεf,lt_min hτa (lt_min hτf (lt_min hτI hτM)),?_⟩
  intro J
  choose A hA hAj using hscalar'
  let U := 1+∑ k∈Finset.range (J+1),A k
  have hsumU : 0≤∑ k∈Finset.range (J+1),A k := Finset.sum_nonneg (fun k _ => zero_le_one.trans (hA k))
  have hU1 : 1≤U := by dsimp [U]; linarith
  have hAU (k : ℕ) (hk : k≤J) : A k≤U := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.range (J+1)) => zero_le_one.trans (hA l))
      (show k∈Finset.range (J+1) by simp; omega)
    dsimp [U]
    linarith
  choose I hI hIj using hIjet
  let M := 1+∑ k∈Finset.range (J+1),I k
  have hsumI : 0≤∑ k∈Finset.range (J+1),I k := Finset.sum_nonneg (fun k _ => (hI k).le)
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
  refine ⟨K,hK,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ G hG L hL hGj xs hxs
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hepsa : ε<εa := hεr.trans_le (min_le_left _ _)
  have hepsf : ε<εf := hεr.trans_le (min_le_right _ _)
  have hta : τ<τa := hτr.trans_le (min_le_left _ _)
  have htf : τ<τf := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htI : τ<τI := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htM : τ<τM := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hpoint,hstrict⟩ := hframe N hN ε τ hε hepsf hτ htf θ hθ
  have hMall : ∀ x : Fin N → ℝ,(preferredContourMatrix τ B.p B.m x).det≠0 := hM N hN τ hτ htM
  have hInv : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹) :=
    contDiff_iff_contDiffAt.mpr (fun x => preferredContourMatrix_inverse_contDiffAt τ B.p B.m
      B.smooth B.m_smooth x (hMall x))
  have hMj (i b : Fin N) (k : ℕ) (hk : k≤J) :
      ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹ i b) θ‖≤M*(N:ℝ)^J := by
    exact (preferred_anchor_matrix_entry_jet_le _ hInv θ k i b).trans
      ((hIj k τ hτ htI.le N hN θ).trans
        (mul_le_mul (hIM k hk) (pow_le_pow_right₀ hn hk) (by positivity) (zero_le_one.trans hM1)))
  have hUj (a : Option (Fin N)) (b : Fin N) (k : ℕ) (hk : k≤J) :
      ‖iteratedFDeriv ℂ k (preferredSeparatedInverseFactor a b) (s,preferredSourceCoordinate τ B.p B.m s θ)‖≤U := by
    apply preferredSeparatedInverseFactor_jet_le a b _ k (zero_le_one.trans hU1) hpoint.inverse_analytic
    intro i
    have hh := hAj k N hN ε τ hε hepsa hτ hta θ hθ i
    exact ⟨hh.1.trans (hAU k hk),hh.2.1.trans (hAU k hk)⟩
  exact preferredFrameJet_angular_norm_at hN τ δ B.p B.m B.smooth B.m_smooth hMall G hG
    s θ hpoint hstrict J hL hU1 hM1 hGj hUj hMj xs hxs

/-- Every actual anchor cell cutoff has the same dimension-uniform
exponential-times-polynomial frame bound, on the entire lifted contour. -/
theorem preferred_actual_anchor_cell_weight_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ a : Fin N,∀ xs : List (Option (Fin N)),xs.length≤J →
      ‖preferredFrameJet τ B.p B.m
        (fun _ x => (preferredCellWeight (.anchor a) preferredPopulationCutoff B.p B.m rcut x:ℂ)) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C^N*(N:ℝ)^(J*J+5*J) := by
  obtain ⟨cap,hcap,hcapa,hcontrol⟩ := preferred_actual_whole_angular_frame_control d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨ε₀,τ₀,hε₀,hτ₀,hcontrol'⟩ := hcontrol B hB
  refine ⟨ε₀,τ₀,hε₀,hτ₀,?_⟩
  intro rcut hrcut hrper J
  obtain ⟨K,hK,hframe⟩ := hcontrol' J
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  obtain ⟨W,hW,hWjet⟩ := preferredCellWeight_anchor_finite_jets B.p B.m rcut B.smooth B.m_smooth hrcut
    B.periodic hmp hrper J
  refine ⟨K*W,one_le_mul_of_one_le_of_one_le hK hW,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ a xs hxs
  let G := fun x : Fin N → ℝ => (preferredCellWeight (.anchor a) preferredPopulationCutoff B.p B.m rcut x:ℂ)
  have hreal : ContDiff ℝ ∞ (preferredCellWeight (.anchor a) preferredPopulationCutoff B.p B.m rcut : (Fin N → ℝ) → ℝ) := by
    have hη := preferredPopulationCutoff_smooth
    have hp := B.smooth
    have hm := B.m_smooth
    unfold preferredCellWeight preferredLowerWeight lowerWeight preferredAnchorWeight occupancy
    fun_prop
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hreal
  have hGj (k : ℕ) (hk : k≤J) : ‖iteratedFDeriv ℝ k G θ‖≤W^N*(N:ℝ)^(3*J) :=
    ofReal_jet_le _ hreal θ k (hWjet N hN θ a k hk)
  have hh := hframe N hN ε τ hε hεr hτ hτr θ hθ G hG
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

end
end IsingBulk.Preferred22
