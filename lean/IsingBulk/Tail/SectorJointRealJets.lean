import IsingBulk.Tail.SignedSectorIntegrals
import IsingBulk.Tail.CompactNormalizationJets
import IsingBulk.Tail.MixedSectorWeights

/-! Full joint real jets of the literal original and named-current sector
weights. Constants are fixed before the dimension and the sector labels. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

theorem finite_periodic_joint_product_jets {I : Type*} [Fintype I]
    (g : I → ℝ → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hper : ∀ i, Function.Periodic (g i) (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ labels : Fin N → I,
      ∀ p : ℂ × (Fin N → ℝ),
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        ∏ i, (g (labels i) (q.2 i):ℂ)) p J 1 (C^N*(N:ℝ)^J) 0 := by
  classical
  choose B hB hb using fun i => periodic_finite_jet_bound (g i) (hg i) (hper i) J
  let C : ℝ := 1+∑ i, B i
  have hsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hBC (i : I) : B i ≤ C := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hB j).le)
      (Finset.mem_univ i)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro N hN labels p
  have hfactor (i : Fin N) : RealScaledJetBound
      (fun q : ℂ × (Fin N → ℝ) => (g (labels i) (q.2 i):ℂ)) p J 1 C 0 := by
    let L : (ℂ × (Fin N → ℝ)) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℂ (Fin N → ℝ))
    have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun q => by
      simpa [L] using (norm_le_pi_norm q.2 i).trans (norm_snd_le q))
    have hsm : ContDiff ℝ ∞ (fun q : ℂ × (Fin N → ℝ) => g (labels i) (q.2 i)) :=
      (hg (labels i)).comp L.contDiff
    refine RealScaledJetBound.of_uniform
      (Complex.ofRealCLM.contDiff.comp hsm).contDiffAt (zero_le_one.trans hC) zero_lt_one le_rfl ?_
    intro k hk
    have hh := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := p) hsm.contDiffAt
      (by simp : (k:ℕ∞ω) ≤ ∞)
    have hc : ‖Complex.ofRealCLM‖ ≤ 1 :=
      Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
    apply (hh.trans (mul_le_of_le_one_left (norm_nonneg _) hc)).trans
    exact (jet_comp_contraction_right L hL _ (hg (labels i)) p k).trans
      ((hb (labels i) k hk (p.2 i)).trans (hBC (labels i)))
  have hh := RealScaledJetBound.finset_prod Finset.univ (fun i _ => hfactor i)
    (zero_le_one.trans hC) zero_lt_one
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  simpa only [Finset.card_univ,Fintype.card_fin,zero_mul,max_eq_right hN1] using hh

theorem original_sector_joint_real_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ q : Fin N, ∀ sigma : Fin N → Fin 3,
      ∀ p : ℂ × (Fin N → ℝ), RealScaledJetBound
        (fun z : ℂ × (Fin N → ℝ) => originalSectorAngularWeight f b outer inner ho hi q sigma z.2)
        p J 1 (C^N*(N:ℝ)^J) 0 := by
  obtain ⟨C,hC,hj⟩ := finite_periodic_joint_product_jets (sectorScalarFamily f b outer inner ho hi)
    (fun l => (sectorScalarFamily_regular f hf b outer inner ho hi l).1)
    (fun l => (sectorScalarFamily_regular f hf b outer inner ho hi l).2) J
  refine ⟨C,hC,?_⟩
  intro N hN q sigma p
  apply (hj N hN (fun i => (sectorOuterRole q i,sigma i,(1:Fin 3))) p).congr
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [← Complex.ofReal_prod,sectorScalarFamily_product,selectorSectorScalar_original_product]
    simp only [originalSectorAngularWeight,Complex.ofReal_mul,mul_comm])

theorem current_sector_joint_real_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      ∀ qS q : Fin N, ∀ sigma : Fin N → Fin 3,
      ∀ p : ℂ × (Fin N → ℝ), RealScaledJetBound
        (fun z : ℂ × (Fin N → ℝ) => currentSectorAngularWeight f τ qS b outer inner ho hi q sigma z.2)
        p J 1 ((2*C)^N*(N:ℝ)^J) 0 := by
  obtain ⟨C,hC,hj⟩ := finite_periodic_joint_product_jets (sectorScalarFamily f b outer inner ho hi)
    (fun l => (sectorScalarFamily_regular f hf b outer inner ho hi l).1)
    (fun l => (sectorScalarFamily_regular f hf b outer inner ho hi l).2) J
  refine ⟨C,hC,?_⟩
  intro N hN τ hτ hτ1 qS q sigma p
  have hh := (hj N hN (fun i => (sectorOuterRole q i,sigma i,if i=qS then (2:Fin 3) else 1)) p).const_mul
    (-2*Complex.I*(τ:ℂ))
  have hc : ‖-2*Complex.I*(τ:ℂ)‖ ≤ 2 := by
    simp only [norm_mul,norm_neg,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hτ]
    norm_num
    linarith
  have hn : (2:ℝ) ≤ 2^N := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN
  have hcost : ‖-2*Complex.I*(τ:ℂ)‖*(C^N*(N:ℝ)^J) ≤ (2*C)^N*(N:ℝ)^J := by
    rw [mul_pow]
    calc
      _ ≤ 2^N*(C^N*(N:ℝ)^J) := mul_le_mul_of_nonneg_right (hc.trans hn) (by positivity)
      _ = _ := by ring
  apply (hh.mono zero_lt_one le_rfl hcost).congr
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [← Complex.ofReal_prod,sectorScalarFamily_product,selectorSectorScalar_current_product]
    simp only [currentSectorAngularWeight,namedCurrentMultiplier,Complex.ofReal_mul]
    ring)

theorem sector_joint_real_jets_common (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ q : Fin N, ∀ sigma : Fin N → Fin 3,
      ∀ p : ℂ × (Fin N → ℝ),
      RealScaledJetBound (fun z : ℂ × (Fin N → ℝ) =>
        originalSectorAngularWeight f b outer inner ho hi q sigma z.2) p J 1 (C^N*(N:ℝ)^J) 0 ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∀ qS : Fin N,
      RealScaledJetBound (fun z : ℂ × (Fin N → ℝ) =>
        currentSectorAngularWeight f τ qS b outer inner ho hi q sigma z.2) p J 1 (C^N*(N:ℝ)^J) 0 := by
  obtain ⟨A,hA,ha⟩ := original_sector_joint_real_jets f hf b outer inner ho hi J
  obtain ⟨B,hB,hb⟩ := current_sector_joint_real_jets f hf b outer inner ho hi J
  refine ⟨A+2*B,by linarith,?_⟩
  intro N hN q sigma p
  constructor
  · apply (ha N hN q sigma p).mono zero_lt_one le_rfl
    gcongr
    linarith
  · intro τ hτ hτ1 qS
    apply (hb N hN τ hτ hτ1 qS q sigma p).mono zero_lt_one le_rfl
    gcongr
    linarith

theorem original_sector_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    ContDiff ℝ ∞ (originalSectorAngularWeight f b outer inner ho hi q sigma) :=
  (complexSelector_contDiff f hf).mul
    (Complex.ofRealCLM.contDiff.comp (nested_sector_smooth b outer inner ho hi q sigma))

theorem current_sector_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (τ b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (qS q : Fin N) (sigma : Fin N → Fin 3) :
    ContDiff ℝ ∞ (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) := by
  have hh := (namedSelectorDerivative_smooth f hf qS)
  exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hh)).mul
    (Complex.ofRealCLM.contDiff.comp (nested_sector_smooth b outer inner ho hi q sigma)))

end
end IsingBulk.Tail
