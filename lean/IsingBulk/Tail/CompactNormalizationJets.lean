import IsingBulk.Tail.RealDeterminantJets
import IsingBulk.Tail.MixedSourceNormalization

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem complexShift_coordinate_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (τ : ℝ) (i : Fin N) : ContDiff ℝ ∞ (fun θ : Fin N → ℝ => complexShift f τ θ i) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp
    (shiftMap_contDiff f τ hf.p_smooth hf.m_smooth))

theorem complexShift_finite_jets (f : SelectorFunctions) (hf : RegularSelector f) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      ∀ i : Fin N, ∀ θ : Fin N → ℝ, ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (fun x => complexShift f τ x i) θ‖ ≤ C := by
  obtain ⟨C,hC,hj⟩ := periodic_retraction_finite_jets f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic J
  refine ⟨C,zero_lt_one.trans_le hC,?_⟩
  intro N hN τ hτ hτ1 i θ k hk
  let R := normalizedRetractionShift N f.p f.m i
  have hR : ContDiff ℝ ∞ R := normalizedRetractionShift_smooth N f.p f.m hf.p_smooth hf.m_smooth i
  have hRc : ContDiff ℝ ∞ (fun x => (R x:ℂ)) := Complex.ofRealCLM.contDiff.comp hR
  have hreal := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := θ) hR.contDiffAt
    (by simp : (k:ℕ∞ω) ≤ ∞)
  have hc : ‖Complex.ofRealCLM‖ ≤ 1 := Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
  have hb : ‖iteratedFDeriv ℝ k (fun x => (R x:ℂ)) θ‖ ≤ C :=
    (hreal.trans (mul_le_of_le_one_left (norm_nonneg _) hc)).trans (hj N hN i θ k hk)
  have he : (fun x => complexShift f τ x i)=(fun x => (τ:ℂ) • (R x:ℂ)) := by
    funext x
    simp only [complexShift,shiftMap,retractionShift_normalized,Complex.ofReal_mul,smul_eq_mul]
    rfl
  rw [he,iteratedFDeriv_const_smul_apply' (hRc.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hτ]
  exact (mul_le_mul_of_nonneg_left hb hτ).trans (mul_le_of_le_one_left (zero_le_one.trans hC) hτ1)

theorem angularJacobian_real_uniform_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ θ : Fin N → ℝ, ∀ i j,
      RealScaledJetBound (fun x => angularJacobian f τ lam x i j) θ J 1 C 0 := by
  obtain ⟨A,hA,hjet⟩ := complexShift_finite_jets f hf (J+1)
  refine ⟨1+A,by linarith,?_⟩
  intro N hN τ lam hτ hτ1 hlam hlam1 θ i j
  have hsm := complexShift_coordinate_smooth f hf τ i
  have hd := real_direction_uniform_jets hsm.contDiffAt hA.le (Pi.single j 1)
    (by simp [Pi.norm_single]) (fun k _ hk => hjet N hN τ hτ hτ1 i θ k hk)
  have hmul := hd.const_mul (lam:ℂ)
  have hmul' := hmul.mono zero_lt_one le_rfl (show ‖(lam:ℂ)‖*A ≤ A from by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlam]
    exact mul_le_of_le_one_left hA.le hlam1)
  have hc := RealScaledJetBound.const θ J (if i=j then Complex.I else 0)
  have hc' := hc.mono zero_lt_one le_rfl (show ‖(if i=j then Complex.I else 0:ℂ)‖ ≤ 1 from by
    split_ifs <;> simp)
  apply (hc'.add hmul').congr
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [angularJacobian_eq_affine f 1 τ lam hf.p_smooth hf.m_smooth x]
    rfl)

theorem angularJacobian_joint_uniform_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ p : ℂ × (Fin N → ℝ), ∀ i j,
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) => angularJacobian f τ lam q.2 i j) p J 1 C 0 := by
  obtain ⟨C,hC,hj⟩ := angularJacobian_real_uniform_jets f hf J
  refine ⟨C,hC,?_⟩
  intro N hN τ lam hτ hτ1 hlam hlam1 p i j
  have hsm : ContDiff ℝ ∞ (fun θ => angularJacobian f τ lam θ i j) := by
    have hh := angularJacobian_joint_contDiff (N := N) f τ hf.p_smooth hf.m_smooth
    exact ((contDiff_apply ℝ ℂ j).comp ((contDiff_apply ℝ (Fin N → ℂ) i).comp hh)).comp
      (contDiff_const.prodMk contDiff_id)
  let L := ContinuousLinearMap.snd ℝ ℂ (Fin N → ℝ)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by simpa [L] using norm_snd_le x)
  refine ⟨(hsm.comp contDiff_snd).contDiffAt,by linarith,?_⟩
  intro k hk
  exact (jet_comp_contraction_right L hL _ hsm p k).trans
    ((hj N hN τ lam hτ hτ1 hlam hlam1 p.2 i j).bound k hk)

theorem mixedDensityNormalization_joint_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ p : ℂ × (Fin N → ℝ),
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) => mixedDensityNormalization f τ lam q.2)
        p J 1 (C^N*(N:ℝ)^J) 0 := by
  obtain ⟨C,hC,hj⟩ := angularJacobian_joint_uniform_jets f hf J
  refine ⟨C,hC,?_⟩
  intro N hN τ lam hτ hτ1 hlam hlam1 p
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hh := real_normalized_determinant_jets (fun q : ℂ × (Fin N → ℝ) => angularJacobian f τ lam q.2)
    p J C (by linarith) (hj N hN τ lam hτ hτ1 hlam hlam1 p)
  rw [max_eq_right hN1] at hh
  let c : ℂ := (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))
  have hc : ‖c‖ ≤ 1 := by
    have hp : (2*Real.pi)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith [Real.pi_gt_three])
    have hn : ‖2*(Real.pi:ℂ)*Complex.I‖=2*Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    change ‖(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))‖ ≤ 1
    rw [norm_zpow,hn,zpow_neg,zpow_natCast,← inv_pow]
    exact pow_le_one₀ (by positivity : 0 ≤ (2*Real.pi)⁻¹) hp
  apply ((hh.const_mul c).mono zero_lt_one le_rfl
    (mul_le_of_le_one_left hh.nonneg hc)).congr
  exact Eventually.of_forall (fun q => by dsimp [mixedDensityNormalization,c]; ring)

end
end IsingBulk.Tail
