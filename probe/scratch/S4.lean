import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray

set_option maxSynthPendingDepth 1
set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry
open GroundTheory.Arith.SchemeCoh

universe w w' u

namespace Probe4

section T

variable {X : TopCat.{u}}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

theorem T1 (F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Ext F G n) : x = x := rfl

theorem T2 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

theorem T3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : Sheaf.H.map (𝟙 G) n x = x := Sheaf.H.map_id_apply x

theorem T4 (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{w'} S.X₃ n) :
    x.comp hS.extClass rfl = x.comp hS.extClass rfl := rfl

end T

section L

attribute [local instance] CategoryTheory.sheafIsAbelian

variable {X : TopCat.{u}}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

theorem L1 (F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Ext F G n) : x = x := rfl

theorem L2 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

theorem L3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : Sheaf.H.map (𝟙 G) n x = x := Sheaf.H.map_id_apply x

theorem L4 (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{w'} S.X₃ n) :
    x.comp hS.extClass rfl = x.comp hS.extClass rfl := rfl

end L

section E

variable {X : TopCat.{u}}
variable [@HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) _ sheafIsAbelian]

theorem E1 (F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Ext F G n) : x = x := rfl

theorem E2 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

theorem E3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : Sheaf.H.map (𝟙 G) n x = x := Sheaf.H.map_id_apply x

theorem E4 (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{w'} S.X₃ n) :
    x.comp hS.extClass rfl = x.comp hS.extClass rfl := rfl

end E

section W

abbrev SheafHasExt.{a, b, c, d} {C : Type d} [Category.{c} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{b}] : Prop :=
  HasExt.{a} (Sheaf J AddCommGrpCat.{b})

variable {X : TopCat.{u}}
variable [SheafHasExt.{w', u} (Opens.grothendieckTopology X)]

theorem W1 (F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Ext F G n) : x = x := rfl

theorem W2 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

theorem W3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : Sheaf.H.map (𝟙 G) n x = x := Sheaf.H.map_id_apply x

theorem W4 (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{w'} S.X₃ n) :
    x.comp hS.extClass rfl = x.comp hS.extClass rfl := rfl

end W

section Print

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 200000
set_option pp.deepTerms true

#check @Probe4.T2
#check @Probe4.L2
#check @Probe4.E2
#check @Probe4.W2
#check @Probe4.L4
#check @TopCat.Sheaf.instAbelian
#print TopCat.Sheaf.instAbelian

end Print

end Probe4
