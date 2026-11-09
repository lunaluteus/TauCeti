/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent endomorphisms and quotients

An endomorphism that vanishes on an invariant submodule `p` and induces a nilpotent endomorphism
of the quotient by `p` is nilpotent (`Submodule.isNilpotent_of_isNilpotent_mapQ`). This is the
converse direction of Mathlib's `Module.End.IsNilpotent.mapQ`, which passes nilpotence to the
quotient.
-/

public section

namespace Submodule

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- An endomorphism that vanishes on an invariant submodule and induces a nilpotent endomorphism
of the quotient is nilpotent. -/
theorem isNilpotent_of_isNilpotent_mapQ (p : Submodule R V)
    (f : Module.End R V) (hp : p ≤ p.comap f) (hzero : ∀ y ∈ p, f y = 0)
    (hn : IsNilpotent (p.mapQ p f hp)) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n + 1, ?_⟩
  ext y
  rw [pow_succ', mul_apply_eq_comp]
  have hymem : (f ^ n) y ∈ p := by
    apply (Submodule.Quotient.mk_eq_zero p).mp
    have hz := LinearMap.congr_fun hn (p.mkQ y)
    rw [← p.mapQ_pow hp n] at hz
    simpa only [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_apply] using hz
  rw [hzero _ hymem, LinearMap.zero_apply]

end Submodule
