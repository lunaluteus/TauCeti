/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantField

/-!
# A rational place forces exact constants

A constant algebraic over the base field is regular at every place. At a rational place its
residue is the residue of a base-field element. Their difference is algebraic and has valuation
less than one, so it must vanish. Thus the existence of a rational place certifies exactness of
the constant field, including for composita with a completely split rational place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.1 and Corollary 3.9.7.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The degree of every place is divisible by the degree of the field of constants**: the
residue field is an algebra over `algebraicClosure k F`, which is regular at every place. -/
theorem finrank_algebraicClosure_dvd_degree (P : Place k F) :
    Module.finrank k (algebraicClosure k F) ∣ P.degree := by
  let : Algebra (algebraicClosure k F) P.integers :=
    ((algebraicClosure k F).val.toRingHom.codRestrict P.integers
      fun x ↦ P.mem_integers_of_mem_algebraicClosure x.2).toAlgebra
  have : IsScalarTower k (algebraicClosure k F) P.integers :=
    .of_algebraMap_eq fun c ↦ Subtype.ext rfl
  have : IsScalarTower k (algebraicClosure k F) P.ResidueField :=
    .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
        IsScalarTower.algebraMap_apply k (algebraicClosure k F) P.integers,
        ← IsScalarTower.algebraMap_apply (algebraicClosure k F) P.integers P.ResidueField]
  rw [P.degree_eq_finrank, ← Module.finrank_mul_finrank k (algebraicClosure k F) P.ResidueField]
  exact dvd_mul_right _ _

/-- If `F / k` has a rational place, every element of `F` algebraic over `k` belongs to `k`.
No function-field or separability hypothesis is needed. -/
theorem isIntegrallyClosedIn_of_degree_eq_one (P : Place k F) (hP : P.degree = 1) :
    IsIntegrallyClosedIn k F := by
  rw [TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic]
  intro x hx
  obtain ⟨c, hc⟩ := (P.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hP)
    x (P.mem_integers_of_mem_algebraicClosure (mem_algebraicClosure_iff.mpr hx))
  refine ⟨c, (sub_eq_zero.mp ?_).symm⟩
  by_contra hne
  have halg : IsAlgebraic k (x - algebraMap k F c) :=
    mem_algebraicClosure_iff.mp <| (algebraicClosure k F).sub_mem
      (mem_algebraicClosure_iff.mpr hx) ((algebraicClosure k F).algebraMap_mem c)
  rw [P.valuation_eq_one_of_isAlgebraic halg hne] at hc
  exact lt_irrefl _ hc

end TauCeti.Place
