import ClosingEnergyAlgebra
import MarkedPruningAssembly
import Scalar
import LogLoss

/-! Spatial-cutoff and marked-angle substitutions after the closing pivot
energy estimate. Original comparison populations and all real powers remain
explicit. The scalar direction dimension is one below the ambient dimension. -/
namespace KakeyaFormal.PivotFourthPower
open Finset MarkedPruningAssembly MarkedSubsetSamples TransverseAngles
noncomputable section
open Classical

/-- Marked recovery preserves the original comparison M and E in (5.10),
even though the recovered family can have fewer tubes. -/
theorem recovered_angle_count {k M : ℕ} {F O : TubeFamily k M}
    {marks : Fin M → Finset (Cell k)} {E : Finset (Cell k)}
    {δ lam xi width R m A B alpha theta kappa : ℝ}
    (P : RecoveredInput F O marks E δ lam xi width R m A B alpha theta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hxi : 0 < xi) (hangle : 2*kappa ≤ theta) :
    xi^2*lam^2*(M:ℝ)^2/(128*δ^2*(E.card:ℝ)) ≤
      ((angles P.family P.family.unionCells kappa).card:ℝ) := by
  have hh := marked_angle_count P.family P.marks P.family.unionCells
    (by positivity : 0 ≤ xi*lam*(M:ℝ)/(8*δ)) P.comparison_pos hangle
    P.marks_subset P.marked_mass
    (by exact_mod_cast card_le_card P.union_subset_E)
    (fun z _ v hv => P.marked_broad z v hv)
  calc
    _ = (xi*lam*(M:ℝ)/(8*δ))^2/(2*(E.card:ℝ)) := by field_simp; ring
    _ ≤ _ := hh

/-- The recovered density is at worst half the original one. Passing a
nonnegative real density power costs a fixed power of two, not a scale loss. -/
theorem recovered_density_power {k M : ℕ} {F O : TubeFamily k M}
    {marks : Fin M → Finset (Cell k)} {E : Finset (Cell k)}
    {δ lam xi width R m A B alpha theta v : ℝ}
    (P : RecoveredInput F O marks E δ lam xi width R m A B alpha theta)
    (hlam : 0 < lam) (hv : 0 ≤ v) : (2:ℝ)^(-v)*lam^v ≤ P.density^v := by
  have hd : lam/2 ≤ P.density := by
    rcases P.density_choice with h | h
    · rw [h]
    · rw [h]
      linarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ lam/2) hd hv
  rw [Real.div_rpow hlam.le (by norm_num : (0:ℝ) ≤ 2)] at hh
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  simpa only [div_eq_mul_inv,mul_comm] using hh

/-- The original base estimate supplies the lower bound needed to control
the `max 1` in the literal pruning cutoff. -/
theorem inverse_base_bound {c E A δ lam M u p : ℝ}
    (hc : 0 < c) (hA : 0 < A) (hδ : 0 < δ) (hlam : 0 < lam) (hM : 0 < M)
    (hbase : c*A⁻¹*δ^u*lam^p*M ≤ E) :
    c ≤ E*A*δ^(-u)*lam^(-p)/M := by
  have hmul := mul_le_mul_of_nonneg_right hbase
    (by positivity : 0 ≤ A*δ^(-u)*lam^(-p)/M)
  have hid : (c*A⁻¹*δ^u*lam^p*M)*(A*δ^(-u)*lam^(-p)/M) = c := by
    rw [Real.rpow_neg hδ.le,Real.rpow_neg hlam.le]
    field_simp
  rw [hid] at hmul
  calc
    _ ≤ E*(A*δ^(-u)*lam^(-p)/M) := hmul
    _ = _ := by ring

/-- An exact max-cutoff bound that requires no enlargement of the pruning
constant. The fixed coefficient is K+1/c_base. -/
theorem max_cutoff_bound {K c Y eta b : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hY : c ≤ Y)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hb : 0 ≤ b) :
    max 1 (K*Y*eta^(-b)) ≤ (K+1/c)*Y*eta^(-b) := by
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos heta heta1 (by linarith : -b ≤ 0)
  have hY0 : 0 < Y := hc.trans_le hY
  have hprod : c ≤ Y*eta^(-b) := hY.trans (by nlinarith)
  have hunit : 1 ≤ (Y*eta^(-b))/c := (le_div_iff₀ hc).mpr (by simpa using hprod)
  have hid : (K+1/c)*Y*eta^(-b) = K*Y*eta^(-b)+(Y*eta^(-b))/c := by ring
  rw [hid]
  apply max_le
  · have hn : 0 ≤ K*Y*eta^(-b) := by positivity
    linarith
  · have hn : 0 ≤ Y*eta^(-b)/c := by positivity
    linarith

/-- Exact marked-fraction normalization eta=xi/[100(J+1)]. -/
theorem marked_budget_power {xi b : ℝ} (hxi : 0 < xi) (J : ℕ) :
    ((xi/100)/((J:ℝ)+1))^(-b) = (100:ℝ)^b*xi^(-b)*((J:ℝ)+1)^b := by
  rw [Real.div_rpow (by positivity : 0 ≤ xi/100) (by positivity : (0:ℝ) ≤ (J:ℝ)+1),
    Real.div_rpow hxi.le (by norm_num : (0:ℝ) ≤ 100),
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 100),
    Real.rpow_neg (by positivity : (0:ℝ) ≤ (J:ℝ)+1)]
  simp only [div_eq_mul_inv,inv_inv]
  ring

/-- The two powers of E in the spatial cutoff and angle population cancel
against E² to give E⁴. Exponents are arbitrary real numbers. -/
theorem fourth_power_substitution
    {E F A δ xi lam M L kappa H c ca CF f g b p v angleMass : ℝ}
    (hE : 0 < E) (hF : 0 < F) (hA : 0 < A) (hδ : 0 < δ)
    (hxi : 0 < xi) (hlam : 0 < lam) (hM : 0 < M) (hL : 0 < L) (hk : 0 < kappa)
    (hc : 0 < c) (hca : 0 < ca) (hCF : 0 < CF)
    (hcut : F ≤ CF*E*A*δ^f*xi^(-b)*L^b*lam^(-p)/M)
    (hangle : ca*xi^2*lam^2*M^2/(δ^2*E) ≤ angleMass)
    (hclosing : c*kappa^H*F⁻¹*δ^g*lam^v*angleMass/L^3 ≤ E^2) :
    (c*ca/CF)*kappa^H*A⁻¹*xi^(b+2)*L^(-(b+3))*δ^(g-f-2)*lam^(v+p+2)*M^3 ≤ E^4 := by
  let Fmax := CF*E*A*δ^f*xi^(-b)*L^b*lam^(-p)/M
  let Amin := ca*xi^2*lam^2*M^2/(δ^2*E)
  have hFmax : 0 < Fmax := by dsimp [Fmax]; positivity
  have hAmin : 0 ≤ Amin := by dsimp [Amin]; positivity
  have hinv : Fmax⁻¹ ≤ F⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hF hcut
  have hcoef : c*kappa^H*Fmax⁻¹*δ^g*lam^v ≤ c*kappa^H*F⁻¹*δ^g*lam^v := by gcongr
  have hprod := mul_le_mul hcoef hangle hAmin (by positivity : 0 ≤ c*kappa^H*F⁻¹*δ^g*lam^v)
  have htotal := (div_le_div_of_nonneg_right hprod (by positivity : 0 ≤ L^3)).trans hclosing
  have hmul := mul_le_mul_of_nonneg_right htotal (sq_nonneg E)
  have hid : (c*kappa^H*Fmax⁻¹*δ^g*lam^v*Amin/L^3)*E^2 =
      (c*ca/CF)*kappa^H*A⁻¹*xi^(b+2)*L^(-(b+3))*δ^(g-f-2)*lam^(v+p+2)*M^3 := by
    dsimp [Fmax,Amin]
    have hx : xi^(b+2) = xi^b*xi^2 := by rw [Real.rpow_add hxi]; norm_num
    have hlog : L^(b+3) = L^b*L^3 := by rw [Real.rpow_add hL]; norm_num
    have hd : δ^(g-f-2) = (δ^g/δ^f)/δ^2 := by
      rw [Real.rpow_sub hδ,Real.rpow_sub hδ]; norm_num
    have hl : lam^(v+p+2) = lam^v*lam^p*lam^2 := by
      rw [Real.rpow_add hlam,Real.rpow_add hlam]; norm_num
    rw [hx,Real.rpow_neg hL.le,hlog,hd,hl,Real.rpow_neg hxi.le,Real.rpow_neg hlam.le]
    field_simp
  rw [hid] at hmul
  calc
    _ ≤ E^2*E^2 := hmul
    _ = _ := by ring

/-- The literal cutoff from MarkedPruningAssembly is bounded by the source
form, including max 1, the original cap coefficient, and the common depth log. -/
theorem actual_cutoff_upper (J : ℕ)
    {E A M δ lam xi L K c m d p eps : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hE : 0 < E) (hA : 0 < A) (hM : 0 < M)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hp : 1 ≤ p) (heps : 0 ≤ eps) (hJ : (J:ℝ)+1 ≤ L)
    (hbase : c*A⁻¹*δ^(m-d+eps)*lam^p*M ≤ E) :
    max 1 (K*E*A*δ^(d-m-eps)*(((xi/100)/((J:ℝ)+1))^(-(p+1)))*lam^(-p)/M) ≤
      ((K+1/c)*(100:ℝ)^(p+1))*E*A*δ^(d-m-2*eps)*xi^(-(p+1))*L^(p+1)*lam^(-p)/M := by
  let Y := E*A*δ^(d-m-eps)*lam^(-p)/M
  let eta := (xi/100)/((J:ℝ)+1)
  have hY : c ≤ Y := by
    have hh := inverse_base_bound hc hA hδ hlam hM hbase
    rw [show -(m-d+eps)=d-m-eps by ring] at hh
    exact hh
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (J:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) J]
  have hh := max_cutoff_bound hK hc hY heta heta1 (by linarith : 0 ≤ p+1)
  have hid : K*E*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/M = K*Y*eta^(-(p+1)) := by dsimp [Y]; ring
  change max 1 (K*E*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/M) ≤ _
  rw [hid]
  refine hh.trans ?_
  have hd := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    (by linarith : d-m-2*eps ≤ d-m-eps)
  have hdepth := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (J:ℝ)+1) hJ (by linarith : 0 ≤ p+1)
  have hpow : eta^(-(p+1)) = (100:ℝ)^(p+1)*xi^(-(p+1))*((J:ℝ)+1)^(p+1) :=
    marked_budget_power hxi J
  calc
    _ = ((K+1/c)*(100:ℝ)^(p+1)*E*A*xi^(-(p+1))*lam^(-p)/M)*
        δ^(d-m-eps)*((J:ℝ)+1)^(p+1) := by rw [hpow]; dsimp [Y]; ring
    _ ≤ ((K+1/c)*(100:ℝ)^(p+1)*E*A*xi^(-(p+1))*lam^(-p)/M)*
        δ^(d-m-2*eps)*L^(p+1) := by gcongr
    _ = _ := by ring

/-- Complete source substitution, with original M and original base cap A
visible. Here n is projective direction dimension. -/
theorem source_fourth_power (n : ℕ)
    {E F A δ xi lam M L kappa c ca CF m d d' p q eps angleMass : ℝ}
    (hE : 0 < E) (hF : 0 < F) (hA : 0 < A) (hδ : 0 < δ)
    (hxi : 0 < xi) (hlam : 0 < lam) (hM : 0 < M) (hL : 0 < L)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (heps : eps ≤ 1)
    (hc : 0 < c) (hca : 0 < ca) (hCF : 0 < CF)
    (hcut : F ≤ CF*E*A*δ^(d-m-2*eps)*xi^(-(p+1))*L^(p+1)*lam^(-p)/M)
    (hangle : ca*xi^2*lam^2*M^2/(δ^2*E) ≤ angleMass)
    (hclosing : c*kappa^(5*(n:ℝ)+6*(q+eps)+6)*F⁻¹*δ^(d-d'-1+eps)*
      lam^(2*q+2+2*eps)*angleMass/L^3 ≤ E^2) :
    (c*ca/CF)*kappa^(5*(n:ℝ)+6*q+12)*A⁻¹*xi^(p+3)*L^(-(p+4))*
      δ^(m-d'-3+3*eps)*lam^(p+2*q+4+2*eps)*M^3 ≤ E^4 := by
  have hangle0 : 0 ≤ angleMass := (by positivity : 0 ≤ ca*xi^2*lam^2*M^2/(δ^2*E)).trans hangle
  have hp := ClosingEnergyAlgebra.error_kappa_weakening n (q := q) hk hk1 heps
  have hweak : c*kappa^(5*(n:ℝ)+6*q+12)*F⁻¹*δ^(d-d'-1+eps)*
      lam^(2*q+2+2*eps)*angleMass/L^3 ≤ E^2 := by
    refine le_trans ?_ hclosing
    gcongr
  have hh := fourth_power_substitution hE hF hA hδ hxi hlam hM hL hk hc hca hCF hcut hangle hweak
  rw [show p+1+2=p+3 by ring,show p+1+3=p+4 by ring,
    show d-d'-1+eps-(d-m-2*eps)-2=m-d'-3+3*eps by ring,
    show 2*q+2+2*eps+p+2=p+2*q+4+2*eps by ring] at hh
  exact hh

/-- Rewriting S=Mδ^m gives exactly the source's ambient scale exponent. -/
theorem population_scale_identity {M δ m d' eps : ℝ} (hδ : 0 < δ) :
    δ^(m-d'-3+3*eps)*M^3 = δ^(-2*m-3-d'+3*eps)*(M*δ^m)^3 := by
  rw [mul_pow,← Real.rpow_natCast (δ^m) 3,← Real.rpow_mul hδ.le]
  norm_num only [Nat.cast_ofNat]
  have hid : -2*m-3-d'+3*eps+m*(3:ℝ)=m-d'-3+3*eps := by ring
  calc
    _ = (δ^(-2*m-3-d'+3*eps)*δ^(m*(3:ℝ)))*M^3 := by rw [← Real.rpow_add hδ,hid]
    _ = _ := by ring

/-- The normalized-population E⁴ bound of (5.3). The base cap coefficient is
still explicit; the source absorbs it into a fixed normalization constant. -/
theorem source_fourth_power_density (n : ℕ)
    {E F A δ xi lam M S L kappa c ca CF m d d' p q eps angleMass : ℝ}
    (hE : 0 < E) (hF : 0 < F) (hA : 0 < A) (hδ : 0 < δ)
    (hxi : 0 < xi) (hlam : 0 < lam) (hM : 0 < M) (hL : 0 < L)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (heps : eps ≤ 1)
    (hc : 0 < c) (hca : 0 < ca) (hCF : 0 < CF) (hS : S=M*δ^m)
    (hcut : F ≤ CF*E*A*δ^(d-m-2*eps)*xi^(-(p+1))*L^(p+1)*lam^(-p)/M)
    (hangle : ca*xi^2*lam^2*M^2/(δ^2*E) ≤ angleMass)
    (hclosing : c*kappa^(5*(n:ℝ)+6*(q+eps)+6)*F⁻¹*δ^(d-d'-1+eps)*
      lam^(2*q+2+2*eps)*angleMass/L^3 ≤ E^2) :
    (c*ca/CF)*kappa^(5*(n:ℝ)+6*q+12)*A⁻¹*xi^(p+3)*L^(-(p+4))*
      δ^(-2*m-3-d'+3*eps)*lam^(p+2*q+4+2*eps)*S^3 ≤ E^4 := by
  have hh := source_fourth_power n hE hF hA hδ hxi hlam hM hL hk hk1 heps hc hca hCF hcut hangle hclosing
  rw [hS]
  have hid := population_scale_identity (M := M) (m := m) (d' := d') (eps := eps) hδ
  calc
    _ = (c*ca/CF)*kappa^(5*(n:ℝ)+6*q+12)*A⁻¹*xi^(p+3)*L^(-(p+4))*
        (δ^(-2*m-3-d'+3*eps)*(M*δ^m)^3)*lam^(p+2*q+4+2*eps) := by ring
    _ = (c*ca/CF)*kappa^(5*(n:ℝ)+6*q+12)*A⁻¹*xi^(p+3)*L^(-(p+4))*
        δ^(m-d'-3+3*eps)*lam^(p+2*q+4+2*eps)*M^3 := by rw [← hid]; ring
    _ ≤ _ := hh

/-- Real quarter-powers undo the fourth power without any integer exponent
restriction on the monomial being rooted. -/
theorem quarter_power {x a : ℝ} (hx : 0 ≤ x) : (x^(a/4))^4 = x^a := by
  rw [← Real.rpow_natCast (x^(a/4)) 4,← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- Taking the fourth root displays exactly the dimension and density maps
used by the endpoint recursion, before conditioning-logarithm absorption. -/
theorem fourth_root_bound
    {E c kappa xi L δ lam S H p q m d' eps : ℝ}
    (hE : 0 ≤ E) (hc : 0 < c) (hk : 0 < kappa) (hxi : 0 < xi)
    (hL : 0 < L) (hδ : 0 < δ) (hlam : 0 < lam) (hS : 0 < S)
    (hfour : c*kappa^H*xi^(p+3)*L^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
      lam^(p+2*q+4+2*eps)*S^3 ≤ E^4) :
    c^(1/4:ℝ)*kappa^(H/4)*xi^((p+3)/4)*L^(-(p+4)/4)*
      δ^(-KakeyaScalar.pivotSet m d'+3*eps/4)*
      lam^(KakeyaScalar.pivotDensity p q+eps/2)*S^(3/4:ℝ) ≤ E := by
  rw [show -KakeyaScalar.pivotSet m d'+3*eps/4 = (-2*m-3-d'+3*eps)/4 by
        unfold KakeyaScalar.pivotSet; ring,
    show KakeyaScalar.pivotDensity p q+eps/2 = (p+2*q+4+2*eps)/4 by
        unfold KakeyaScalar.pivotDensity; ring]
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) hE
  simp only [mul_pow]
  rw [quarter_power hc.le,quarter_power hk.le,quarter_power hxi.le,quarter_power hL.le,
    quarter_power hδ.le,quarter_power hlam.le,quarter_power hS.le]
  norm_num only [Real.rpow_one,Real.rpow_ofNat]
  exact hfour

/-- A fixed population upper bound converts S^(3/4) to S with the exact
fixed coefficient required in (5.35). -/
theorem population_linearization {S C₀ : ℝ} (hS : 0 < S) (hSC : S ≤ C₀) :
    C₀^(-(1/4:ℝ))*S ≤ S^(3/4:ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos hS hSC (by norm_num : -(1/4:ℝ) ≤ 0)
  calc
    _ ≤ S^(-(1/4:ℝ))*S := mul_le_mul_of_nonneg_right hh hS.le
    _ = S^(-(1/4:ℝ))*S^(1:ℝ) := by rw [Real.rpow_one]
    _ = S^(-(1/4:ℝ)+1) := (Real.rpow_add hS _ _).symm
    _ = _ := by congr 1; norm_num

end
end KakeyaFormal.PivotFourthPower
