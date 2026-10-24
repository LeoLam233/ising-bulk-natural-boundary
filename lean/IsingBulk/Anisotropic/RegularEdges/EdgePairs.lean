import IsingBulk.Anisotropic.RegularEdges.RadialNeighborhood
import IsingBulk.Anisotropic.RegularEdges.MatchedPfaffian
import IsingBulk.Anisotropic.RegularEdges.OddGhost

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Schur

theorem complex_pair_cancellation {B C y w u v : ℂ}
    (hy : y≠0) (hw : w≠0) (hu : u≠0) (hv : v≠0)
    (hyw : 1-y*w≠0) (huv : 1-u*v≠0)
    (htu : u+u⁻¹=2*(C-B*(y+y⁻¹)/2))
    (htv : v+v⁻¹=2*(C-B*(w+w⁻¹)/2)) :
    pairKernel u v*pairKernel y w=B*canceledPair y w u v := by
  have hrel : (u-v)*(1-u*v)*y*w = -B*(y-w)*(1-y*w)*u*v := by
    have hh := congrArg₂ (fun a b : ℂ => a-b) htu htv
    field_simp [hu,hv,hy,hw] at hh
    linear_combination -hh
  unfold pairKernel canceledPair
  field_simp [huv,hyw,hy,hw]
  linear_combination (y-w)*hrel

theorem edgeCircleRoot_pair_cancellation (b : ℝ) (B : ℂ → ℂ) (u : ℂ) {y w : ℂ}
    (hy : y≠0) (hw : w≠0) (hyw : 1-y*w≠0)
    (hroot : 1-edgeCircleRoot b B u y*edgeCircleRoot b B u w≠0) :
    pairKernel (edgeCircleRoot b B u y) (edgeCircleRoot b B u w)*pairKernel y w =
      B u*canceledPair y w (edgeCircleRoot b B u y) (edgeCircleRoot b B u w) := by
  apply complex_pair_cancellation (C := (b:ℂ)+u+B u) hy hw
    (continuedRoot_nonzero _) (continuedRoot_nonzero _) hyw hroot
  · have hh := quadratic_root_trace (continuedRoot_quadratic (edgeCircleW b B u y))
    rw [hh]
    unfold edgeCircleW
    ring
  · have hh := quadratic_root_trace (continuedRoot_quadratic (edgeCircleW b B u w))
    rw [hh]
    unfold edgeCircleW
    ring

theorem list_pairProduct_mul (K L : ℂ → ℂ → ℂ) (xs : List ℂ) :
    IsingBulk.Schur.pairProduct (fun a b => K a b*L a b) xs =
      IsingBulk.Schur.pairProduct K xs*IsingBulk.Schur.pairProduct L xs := by
  induction xs with
  | nil => simp [IsingBulk.Schur.pairProduct]
  | cons a xs ih =>
    simp only [IsingBulk.Schur.pairProduct,List.prod_map_mul,ih]
    ring

theorem list_pairProduct_congr (K L : ℂ → ℂ → ℂ) (xs : List ℂ)
    (h : ∀ a ∈ xs, ∀ b ∈ xs, K a b=L a b) :
    IsingBulk.Schur.pairProduct K xs=IsingBulk.Schur.pairProduct L xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [IsingBulk.Schur.pairProduct]
    rw [ih (fun b hb c hc => h b (by simp [hb]) c (by simp [hc]))]
    congr 2
    apply List.map_congr_left
    intro b hb
    exact h a (by simp) b (by simp [hb])

/-- Pole-free complete products retain every unmatched root contraction. -/
theorem even_complete_pair_bound (K P : ℂ → ℂ → ℂ)
    (hsym : ∀ a b, ‖K a b‖=‖K b a‖) (n : ℕ) (xs : List ℂ)
    (hlen : xs.length=2*n) {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    (hd : ∀ a ∈ xs, ∀ b ∈ xs, 1-a*b≠0)
    (hK : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖≤r)
    (hP : ∀ a ∈ xs, ∀ b ∈ xs, ‖P a b‖≤C)
    (he : ∀ a ∈ xs, ∀ b ∈ xs, K a b*pairKernel a b=P a b) :
    ‖IsingBulk.Schur.pairProduct P xs‖ ≤ (matchingCount n:ℝ)*C^n*r^(2*n*(n-1)) := by
  rw [← list_pairProduct_congr _ P xs he,list_pairProduct_mul]
  have hh := IsingBulk.HT.First.schur_even_list n xs hlen hd
  change pfaffian pairKernel n xs=IsingBulk.Schur.pairProduct pairKernel xs at hh
  rw [← hh]
  exact matched_pfaffian_bound K pairKernel hsym n xs hlen hr hC hK
    (fun a ha b hb => by rw [he a ha b hb]; exact hP a ha b hb)

theorem odd_complete_pair_bound (K P : ℂ → ℂ → ℂ)
    (hsym : ∀ a b, ‖K a b‖=‖K b a‖) (n : ℕ) (xs : List ℂ)
    (hlen : xs.length=2*n+1) {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    (hd : ∀ a ∈ xs, ∀ b ∈ xs, 1-a*b≠0) (hg : ∀ a ∈ xs, a≠-1)
    (hK : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖≤r)
    (hP : ∀ a ∈ xs, ∀ b ∈ xs, ‖P a b‖≤C)
    (he : ∀ a ∈ xs, ∀ b ∈ xs, K a b*pairKernel a b=P a b) :
    ‖IsingBulk.Schur.pairProduct P xs‖ ≤ (matchingCount (n+1):ℝ)*C^n*r^(2*n*n) := by
  rw [← list_pairProduct_congr _ P xs he,list_pairProduct_mul,norm_mul]
  have hh := schur_odd_front_norm n xs hlen hd hg
  change ‖pfaffian pairKernel (n+1) ((-1)::xs)‖=‖IsingBulk.Schur.pairProduct pairKernel xs‖ at hh
  rw [← hh,← norm_mul]
  apply odd_matched_pfaffian_bound K pairKernel hsym n (-1) xs hlen hr hC hK
    (fun a ha b hb => by rw [he a ha b hb]; exact hP a ha b hb)
  intro a ha
  have heq : pairKernel (-1) a = -pairKernel a (-1) := by unfold pairKernel; ring
  rw [heq,norm_neg]
  change ‖(a-(-1))/(1-a*(-1))‖≤1
  rw [IsingBulk.HT.First.schur_ghost_entry (hg a ha),norm_one]
end
end IsingBulk.Anisotropic.RegularEdges
