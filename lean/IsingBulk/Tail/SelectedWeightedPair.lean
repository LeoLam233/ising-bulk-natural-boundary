import IsingBulk.Tail.CircularConvolution
import IsingBulk.Tail.WeightedPairingIntegral

/-! The compact Gaussian discount is inserted into vertex weights before
integrating a matching. Only an L¹ bound on the branch weight is needed. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set
open scoped Topology

theorem selected_pair_majorant_integral {T K₀ d : ℝ} (hT : 0 ≤ T)
    {w K : ℝ → ℝ} (hw : IntegrableOn w (Icc 0 T)) (hK : Continuous K)
    (hp : Function.Periodic K T) :
    IntegrableOn (fun p : ℝ × ℝ => K₀*(w p.1*w p.2)+d^2*K (p.1+p.2))
      (Icc 0 T ×ˢ Icc 0 T) ∧
    (∫ p in Icc 0 T ×ˢ Icc 0 T, K₀*(w p.1*w p.2)+d^2*K (p.1+p.2)) =
      K₀*(∫ x in Icc 0 T,w x)^2+d^2*T*(∫ x in Icc 0 T,K x) := by
  let B := Icc (0:ℝ) T
  have hwi : IntegrableOn (fun p : ℝ × ℝ => w p.1*w p.2) (B ×ˢ B) := by
    rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict]
    exact hw.mul_prod hw
  have hki : IntegrableOn (fun p : ℝ × ℝ => K (p.1+p.2)) (B ×ˢ B) :=
    (hK.comp (continuous_fst.add continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  refine ⟨(hwi.const_mul K₀).add (hki.const_mul (d^2)), ?_⟩
  rw [integral_add (hwi.const_mul K₀) (hki.const_mul (d^2)),
    integral_const_mul,integral_const_mul]
  have hew : (∫ p in B ×ˢ B,w p.1*w p.2) = (∫ x in B,w x)^2 := by
    rw [Measure.volume_eq_prod,setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
    simp_rw [integral_const_mul]
    rw [integral_mul_const,pow_two]
  have hek : (∫ p in B ×ˢ B,K (p.1+p.2)) = T*(∫ x in B,K x) := by
    rw [Measure.volume_eq_prod,setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
    change (∫ x in Icc 0 T, ∫ y in Icc 0 T, K (x+y)) = _
    simp_rw [periodic_kernel_integral_translate hT hp]
    simp [B,MeasureTheory.integral_const,hT]
  change K₀*(∫ p in B ×ˢ B,w p.1*w p.2)+d^2*(∫ p in B ×ˢ B,K (p.1+p.2)) = _
  rw [hew,hek]
  ring

/-- Pointwise branch/compact splitting removes the exceptional mask without
squaring the branch singularity. -/
theorem discounted_pair_pointwise {w : ℝ → ℝ} {c : ℝ → Prop}
    [DecidablePred c] {A : ℝ → ℝ → ℝ} {K : ℝ → ℝ} {K₀ d : ℝ}
    (hw : ∀ x, 0 ≤ w x) (hd : 0 ≤ d) (hK : ∀ t, 0 ≤ K t)
    (hc : ∀ x, c x → w x ≤ d)
    (hA : ∀ x y, A x y ≤ K₀ + if c x ∧ c y then K (x+y) else 0)
    (x y : ℝ) :
    w x*w y*A x y ≤ K₀*(w x*w y)+d^2*K (x+y) := by
  have h := mul_le_mul_of_nonneg_left (hA x y) (mul_nonneg (hw x) (hw y))
  by_cases hh : c x ∧ c y
  · simp only [ite_eq_left hh] at h
    have hm := mul_le_mul (hc x hh.1) (hc y hh.2) (hw y) hd
    have hk := mul_le_mul_of_nonneg_right hm (hK (x+y))
    nlinarith
  · simp only [ite_eq_right hh,add_zero] at h
    have hk := mul_nonneg (sq_nonneg d) (hK (x+y))
    nlinarith

/-- The two-angle integral and its integrability are obtained by domination,
not supplied as a bound hypothesis. -/
theorem selected_weighted_pair_integral_le {T K₀ d : ℝ} (hT : 0 ≤ T)
    {w K : ℝ → ℝ} (hw : IntegrableOn w (Icc 0 T)) (hK : Continuous K)
    (hp : Function.Periodic K T) {F : ℝ × ℝ → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Icc 0 T ×ˢ Icc 0 T)))
    (hF0 : ∀ p, 0 ≤ F p)
    (hF : ∀ p, F p ≤ K₀*(w p.1*w p.2)+d^2*K (p.1+p.2)) :
    IntegrableOn F (Icc 0 T ×ˢ Icc 0 T) ∧
    (∫ p in Icc 0 T ×ˢ Icc 0 T,F p) ≤
      K₀*(∫ x in Icc 0 T,w x)^2+d^2*T*(∫ x in Icc 0 T,K x) := by
  obtain ⟨hGi,hGe⟩ := selected_pair_majorant_integral (K₀ := K₀) (d := d) hT hw hK hp
  have hFi := hGi.mono' hFm (Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hF0 p)]
    exact hF p))
  exact ⟨hFi,(integral_mono hFi hGi hF).trans_eq hGe⟩

theorem selected_discount_uniform {K₀ C T D A W J L : ℝ}
    (hK₀ : 0 ≤ K₀) (_hC : 0 ≤ C) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hW0 : 0 ≤ W) (hWA : W ≤ A) (hJL : J ≤ D*L) (hL : 1 ≤ L) :
    K₀*W^2+(C/L)^2*T*J ≤ K₀*A^2+C^2*T*D := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hA : 0 ≤ A := hW0.trans hWA
  have hsq : W^2 ≤ A^2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hJL (mul_nonneg (sq_nonneg (C/L)) hT)
  have he : (C/L)^2*T*(D*L) = C^2*T*D/L := by field_simp
  rw [he] at ht
  have hn : 0 ≤ C^2*T*D := mul_nonneg (mul_nonneg (sq_nonneg C) hT) hD
  have hd : C^2*T*D/L ≤ C^2*T*D := (div_le_self hn hL)
  exact add_le_add (mul_le_mul_of_nonneg_left hsq hK₀) (ht.trans hd)

/-- A measurable compact/core partition preserves the integrable branch
majorant and costs only the discounted constant on compact points. -/
theorem discounted_vertex_integrable {T d : ℝ} (hT : 0 ≤ T) (hd : 0 ≤ d)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 T)) (hg0 : ∀ x, 0 ≤ g x)
    (S : Set ℝ) [DecidablePred (· ∈ S)] (hS : MeasurableSet S) :
    let w := S.piecewise (fun _ => d) g
    IntegrableOn w (Icc 0 T) ∧ (∀ x, 0 ≤ w x) ∧
      (∫ x in Icc 0 T,w x) ≤ (∫ x in Icc 0 T,g x)+d*T := by
  classical
  dsimp only
  have hc : IntegrableOn (fun _ : ℝ => d) (Icc 0 T) := continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hw := Integrable.piecewise hS hc.integrableOn hg.integrableOn
  refine ⟨hw, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S <;> simp [Set.piecewise,hx,hd,hg0 x]
  · have hb : ∀ x, S.piecewise (fun _ => d) g x ≤ g x+d := by
      intro x
      by_cases hx : x ∈ S <;> simp [Set.piecewise,hx] <;> linarith [hg0 x]
    have hi := integral_mono hw (hg.add hc) hb
    simp only [Pi.add_apply] at hi
    rw [integral_add hg hc] at hi
    simpa [integral_const,hT,mul_comm] using hi

/-- Convert the genuinely integrable two-angle kernel, including measurable
compact masks, to the finite-product measure used by matching enumeration. -/
theorem selected_pair_pi_integrable (T : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (Function.uncurry f) (Icc 0 T ×ˢ Icc 0 T)) :
    Integrable (fun v : Fin 2 → ℝ => f (v 0) (v 1))
      (Measure.pi (fun _ => volume.restrict (Icc 0 T))) := by
  rw [← (measurePreserving_piFinTwo
    (fun _ : Fin 2 => volume.restrict (Icc (0:ℝ) T))).symm.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
  simp only [Function.comp_def,MeasurableEquiv.piFinTwo_symm_apply]
  rw [Measure.prod_restrict]
  exact hf

end
end IsingBulk.Tail
