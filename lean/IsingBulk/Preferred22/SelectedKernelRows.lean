import IsingBulk.Preferred22.SelectedGaugeBounds
import IsingBulk.Preferred22.SelectedKernelSourceGeometry
import IsingBulk.Preferred22.Hadamard

/-! Genuine occupancy counting for the selected kernel. Exceptional
opposite-plateau entries are charged to the actual real bump mass of the
column. Their summed square therefore costs one particle factor. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Matrix
open Set
set_option maxHeartbeats 1500000

lemma preferred_occupancy_row_sum {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (u : Fin N → ℝ) {P C τ : ℝ} (hP : 0<P) (hC : 0≤C)
    (hτ : 0<τ) (hτ1 : τ≤1) (hsum : ∑ j,u j=P)
    (hA : ∀ i j,‖A i j‖^2≤C+C*(N:ℝ)/(τ*P)*u j) :
    ∀ i,∑ j,‖A i j‖^2≤2*C*(N:ℝ)/τ := by
  intro i
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hA i j)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,hsum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have he : (N:ℝ)*C+C*(N:ℝ)/(τ*P)*P=C*(N:ℝ)+C*(N:ℝ)/τ := by
    field_simp
  rw [he] at hs
  have hh : C*(N:ℝ)≤C*(N:ℝ)/τ := by
    apply (le_div_iff₀ hτ).mpr
    exact (mul_le_mul_of_nonneg_left hτ1 (by positivity : 0≤C*(N:ℝ))).trans_eq (mul_one _)
  calc
    _ ≤ C*(N:ℝ)+C*(N:ℝ)/τ := hs
    _ ≤ C*(N:ℝ)/τ+C*(N:ℝ)/τ := add_le_add hh le_rfl
    _ = 2*C*(N:ℝ)/τ := by ring

lemma preferred_dispersion_factor_margin {W : ℂ} {R g : ℝ}
    (hR : ‖W‖≤R) (hg : g≤‖W^2-1‖) : g≤(R+1)*‖W-1‖ := by
  have he : W^2-1=(W-1)*(W+1) := by ring
  rw [he,norm_mul] at hg
  have hplus : ‖W+1‖≤R+1 := (norm_add_le _ _).trans (by simpa only [norm_one] using add_le_add hR (le_refl (1:ℝ)))
  exact hg.trans ((mul_le_mul_of_nonneg_left hplus (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem preferred_selected_kernel_occupancy_bound {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (θ : Fin N → ℝ)
    (y z W : Fin N → ℂ) (S : ℂ) {E K R c L g γ τ : ℝ}
    (hE : 0<E) (hK : 0<K) (hR : 0≤R) (hc : 0<c) (hL : 0<L)
    (hg : 0<g) (hγ : 0<γ) (hτ : 0<τ)
    (hθ : ∀ i,θ i∈Icc (-Real.pi) Real.pi)
    (hpop : 0<occupancy B.p θ+occupancy B.m θ)
    (hyn : ∀ i,y i≠0) (hzn : ∀ i,z i≠0)
    (hyE : ∀ i,‖y i‖≤E) (hyiE : ∀ i,‖(y i)⁻¹‖≤E)
    (hz1 : ∀ i,‖z i‖≤1) (hziK : ∀ i,‖(z i)⁻¹‖≤K)
    (hWR : ∀ i,‖W i‖≤R)
    (hdisp : ∀ i,y i+(y i)⁻¹+z i+(z i)⁻¹=2*S)
    (hDn : ∀ i j,1-z i*z j≠0)
    (hpair : ∀ i j,c*(‖W i-1‖+‖W j-1‖)≤‖1-z i*z j‖^2)
    (hreg : ∀ i,B.p (θ i)≠1 → B.m (θ i)≠1 → g≤‖(W i)^2-1‖)
    (hsame : ∀ i j,(θ i,θ j)∈preferredSamePlateauPairs d B → L≤‖1-y i*y j‖)
    (him : ∀ i,γ*τ/(N:ℝ)*(occupancy B.p θ*B.m (θ i)+occupancy B.m θ*B.p (θ i))≤(W i).im) :
    ∀ i j,‖gaugeKernel y z i j‖^2≤
      (4*(E*K)^2/L^2+4*E^4*(R+1)/(c*g)+4*E^4/(c*γ))+
      (4*(E*K)^2/L^2+4*E^4*(R+1)/(c*g)+4*E^4/(c*γ))*(N:ℝ)/
        (τ*(occupancy B.p θ+occupancy B.m θ))*(B.p (θ j)+B.m (θ j)) := by
  let C₁ := 4*(E*K)^2/L^2
  let C₂ := 4*E^4*(R+1)/(c*g)
  let C₃ := 4*E^4/(c*γ)
  let C := C₁+C₂+C₃
  let P := occupancy B.p θ
  let Q := occupancy B.m θ
  have hP : 0≤P := Finset.sum_nonneg (fun i _ => B.lower_bound _)
  have hQ : 0≤Q := Finset.sum_nonneg (fun i _ => B.lower_bound _)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hC₁ : 0≤C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0≤C₂ := by dsimp only [C₂]; positivity
  have hC₃ : 0≤C₃ := by dsimp only [C₃]; positivity
  have hC : 0≤C := by dsimp only [C]; positivity
  have hC1 : C₁≤C := by dsimp only [C]; linarith
  have hC2 : C₂≤C := by dsimp only [C]; linarith
  have hC3 : C₃≤C := by dsimp only [C]; linarith
  have hPQ : 0<P+Q := hpop
  have hbase (i j : Fin N) : ‖gaugeKernel y z i j‖^2≤4*E^4/‖1-z i*z j‖^2 :=
    preferred_gaugeKernel_direct_squared_bound y z i j hE.le
      (hyE i) (hyE j) (hyiE i) (hyiE j) (hz1 i) (hz1 j)
  have hregular (i j : Fin N) (hgi : g≤‖(W i)^2-1‖ ∨ g≤‖(W j)^2-1‖) :
      ‖gaugeKernel y z i j‖^2≤C₂ := by
    have hm : g/(R+1)≤‖W i-1‖+‖W j-1‖ := by
      apply (div_le_iff₀ (by positivity : 0<R+1)).mpr
      rcases hgi with hi|hj
      · have hh := preferred_dispersion_factor_margin (hWR i) hi
        nlinarith [norm_nonneg (W j-1)]
      · have hh := preferred_dispersion_factor_margin (hWR j) hj
        nlinarith [norm_nonneg (W i-1)]
    have hd : c*g/(R+1)≤‖1-z i*z j‖^2 := by
      calc
        _ = c*(g/(R+1)) := by ring
        _ ≤ c*(‖W i-1‖+‖W j-1‖) := mul_le_mul_of_nonneg_left hm hc.le
        _ ≤ _ := hpair i j
    calc
      _ ≤ 4*E^4/‖1-z i*z j‖^2 := hbase i j
      _ ≤ 4*E^4/(c*g/(R+1)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = C₂ := by dsimp only [C₂]; field_simp
  have hsamebound (i j : Fin N) (hh : (θ i,θ j)∈preferredSamePlateauPairs d B) :
      ‖gaugeKernel y z i j‖^2≤C₁ := by
    have hy := hsame i j hh
    have hy0 := norm_pos_iff.mp (hL.trans_le hy)
    calc
      _ ≤ 4*(E*K)^2/‖1-y i*y j‖^2 :=
        preferred_gaugeKernel_same_squared_bound y z i j S hE.le hK.le
          (hyn i) (hyn j) (hzn i) (hzn j) (hdisp i) (hdisp j) (hDn i j) hy0
          (hyE i) (hyE j) (hziK i) (hziK j) (hz1 i) (hz1 j)
      _ ≤ C₁ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hL)
        (sq_le_sq₀ hL.le (norm_nonneg _) |>.mpr hy)
  have hopposite (i j : Fin N)
      (hh : (B.p (θ i)=1 ∧ B.m (θ j)=1) ∨ (B.m (θ i)=1 ∧ B.p (θ j)=1)) :
      ‖gaugeKernel y z i j‖^2≤C₃*(N:ℝ)/(τ*(P+Q)) := by
    have hweight : P+Q≤P*B.m (θ i)+Q*B.p (θ i)+(P*B.m (θ j)+Q*B.p (θ j)) := by
      rcases hh with hp|hm
      · rw [hp.1,hp.2]
        simp only [mul_one]
        have hh₁ : 0≤P*B.m (θ i) := mul_nonneg hP (B.lower_bound _)
        have hh₂ : 0≤Q*B.p (θ j) := mul_nonneg hQ (B.lower_bound _)
        linarith only [hh₁,hh₂]
      · rw [hm.1,hm.2]
        simp only [mul_one]
        have hh₁ : 0≤Q*B.p (θ i) := mul_nonneg hQ (B.lower_bound _)
        have hh₂ : 0≤P*B.m (θ j) := mul_nonneg hP (B.lower_bound _)
        linarith only [hh₁,hh₂]
    have hWsum : γ*τ/(N:ℝ)*(P+Q)≤‖W i-1‖+‖W j-1‖ := by
      have hh := mul_le_mul_of_nonneg_left hweight (by positivity : 0≤γ*τ/(N:ℝ))
      have hri := Complex.im_le_norm (W i-1)
      have hrj := Complex.im_le_norm (W j-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero] at hri hrj
      nlinarith [him i,him j]
    have hd : c*γ*τ/(N:ℝ)*(P+Q)≤‖1-z i*z j‖^2 := by
      calc
        _ = c*(γ*τ/(N:ℝ)*(P+Q)) := by ring
        _ ≤ c*(‖W i-1‖+‖W j-1‖) := mul_le_mul_of_nonneg_left hWsum hc.le
        _ ≤ _ := hpair i j
    calc
      _ ≤ 4*E^4/‖1-z i*z j‖^2 := hbase i j
      _ ≤ 4*E^4/(c*γ*τ/(N:ℝ)*(P+Q)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = C₃*(N:ℝ)/(τ*(P+Q)) := by dsimp only [C₃]; field_simp
  intro i j
  change ‖gaugeKernel y z i j‖^2≤C+C*(N:ℝ)/(τ*(P+Q))*(B.p (θ j)+B.m (θ j))
  have hrest : 0≤C*(N:ℝ)/(τ*(P+Q))*(B.p (θ j)+B.m (θ j)) := by
    apply mul_nonneg (by positivity)
    exact add_nonneg (B.lower_bound _) (B.lower_bound _)
  by_cases hip : B.p (θ i)=1 ∨ B.m (θ i)=1
  · by_cases hjp : B.p (θ j)=1 ∨ B.m (θ j)=1
    · rcases hip with hip|him' <;> rcases hjp with hjp|hjm
      · exact (hsamebound i j ⟨⟨hθ i,hθ j⟩,Or.inl ⟨hip,hjp⟩⟩).trans (by linarith)
      · have hb := hopposite i j (Or.inl ⟨hip,hjm⟩)
        have hw : 1≤B.p (θ j)+B.m (θ j) := by rw [hjm]; linarith [B.lower_bound (θ j)]
        have h₁ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hNr.le) (by positivity : 0≤τ*(P+Q))
        have h₂ := mul_le_mul_of_nonneg_left hw (by positivity : 0≤C*(N:ℝ)/(τ*(P+Q)))
        nlinarith
      · have hb := hopposite i j (Or.inr ⟨him',hjp⟩)
        have hw : 1≤B.p (θ j)+B.m (θ j) := by
          rw [hjp]
          have hm : 0≤B.m (θ j) := B.lower_bound _
          linarith only [hm]
        have h₁ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hNr.le) (by positivity : 0≤τ*(P+Q))
        have h₂ := mul_le_mul_of_nonneg_left hw (by positivity : 0≤C*(N:ℝ)/(τ*(P+Q)))
        nlinarith
      · exact (hsamebound i j ⟨⟨hθ i,hθ j⟩,Or.inr ⟨him',hjm⟩⟩).trans (by linarith)
    · have hjp' := not_or.mp hjp
      exact (hregular i j (Or.inr (hreg j hjp'.1 hjp'.2))).trans (by linarith)
  · have hip' := not_or.mp hip
    exact (hregular i j (Or.inl (hreg i hip'.1 hip'.2))).trans (by linarith)

end
end IsingBulk.Preferred22
