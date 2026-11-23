import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH

set_option maxSynthPendingDepth 1
set_option autoImplicit false

open CategoryTheory Limits Opposite Abelian
open GroundTheory.Arith.SchemeCoh

universe w' v u

namespace Probe

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section T

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

set_option diagnostics true
set_option diagnostics.threshold 5
set_option Elab.async false

theorem t1 (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : Sheaf.H F n) : x = x := rfl

theorem t2 (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) : (0 : Sheaf.H F n) = 0 := rfl

theorem t3 (F : Sheaf J AddCommGrpCat.{v}) [Injective F] {n : ℕ} (x : Sheaf.H F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_injective x

theorem t3' (F : Sheaf J AddCommGrpCat.{v}) [Injective F] {n : ℕ}
    (x : Ext ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))) F (n + 1)) :
    x = 0 :=
  Ext.eq_zero_of_injective x

theorem t4 (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map (𝟙 F) n x = x :=
  Sheaf.H.map_id_apply x

theorem t5 (n : ℕ) (x : Sheaf.H S.X₃ n) : x = x := rfl

theorem t6 (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    H.δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl

include hS in
theorem t7 {n : ℕ} (y : Sheaf.H S.X₂ n) (hy : Sheaf.H.map S.g n y = 0) :
    ∃ x : Sheaf.H S.X₁ n, Sheaf.H.map S.f n x = y :=
  Sheaf.H.longSequence_exact₂ hS y hy

theorem t8 (X Y : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : Ext X Y n) : x = x := rfl

end T

section Print

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

set_option pp.explicit true
set_option pp.maxSteps 200000
set_option pp.deepTerms true

#check @Sheaf.H
#print CategoryTheory.Sheaf.H
#print CategoryTheory.HasExt
#print CategoryTheory.Abelian.Ext
#check @Probe.t1
#check @Probe.t3
#check @Ext.eq_zero_of_injective

end Print

end Probe
