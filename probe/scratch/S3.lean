import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH

set_option maxSynthPendingDepth 1
set_option autoImplicit false

open CategoryTheory Limits Opposite Abelian

universe w' w v u

namespace Probe

section A

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

theorem A0 (X Y : Sheaf J AddCommGrpCat.{v}) (f : X ⟶ Y) : f = f := rfl

theorem A1 (X Y : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : Ext X Y n) : x = x := rfl

theorem A2 (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : Sheaf.H F n) : x = x := rfl

theorem A4 (X Y : Sheaf J AddCommGrpCat.{v}) (f g : X ⟶ Y) : f + g = f + g := rfl

theorem A5 (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map (𝟙 F) n x = x := Sheaf.H.map_id_apply x

end A

section B

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

theorem B0 (X Y : Sheaf J AddCommGrpCat.{w}) (f : X ⟶ Y) : f = f := rfl

theorem B1 (X Y : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : Ext X Y n) : x = x := rfl

theorem B2 (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : Sheaf.H F n) : x = x := rfl

theorem B4 (X Y : Sheaf J AddCommGrpCat.{w}) (f g : X ⟶ Y) : f + g = f + g := rfl

theorem B5 (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map (𝟙 F) n x = x := Sheaf.H.map_id_apply x

end B

section Print

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 200000
set_option pp.deepTerms true

#check @Probe.A1
#check @Probe.A2
#check @Probe.B2
#check @Sheaf.H
#check @Abelian.Ext
#check @sheafIsAbelian
#check @ObjectProperty.FullSubcategory.category
#check @Sheaf

end Print

end Probe
