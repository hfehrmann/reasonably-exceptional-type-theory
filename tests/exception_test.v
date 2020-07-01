
Require Import Effects.Exception.

Set Printing Universes.
Set Printing Implicit.

Effect Translate nat.
Effect Translate bool.
Effect Translate list.
Effect Translate eq.
Effect Translate True.

Inductive mTest1 (A: Type): Type -> Prop :=
| cmTest11: mTest1 A bool
| cmTest12: mTest1 A nat -> mTest3 A -> mTest2 A bool 0 -> mTest1 A bool
| cmTest13: mTest2 A nat 10 -> mTest1 A bool
with
mTest2 (A:Type): Type -> nat -> Prop :=
| cmTest21: mTest1 A bool -> mTest2 A nat 10
with
mTest3 (A: Type): Prop :=
| cmTest31: mTest1 A bool -> mTest2 A nat 10-> mTest3 A
with
mTest4 (A: Type): Prop :=
| cmTest41: mTest4 A
| cmTest42: mTest1 A bool -> mTest2 A nat 10 -> mTest3 A -> mTest4 A -> mTest4 A.

Effect Translate mTest1.

Definition constructorTest := cmTest42 (list nat) (cmTest11 (list nat))
                                       (cmTest21 (list nat) (cmTest11 (list nat))) 
                                       (cmTest31 (list nat) (cmTest11 (list nat))
                                                 (cmTest21 (list nat) (cmTest11 (list nat))))
                                       (cmTest41 (list nat)).

Effect Translate constructorTest.

Definition match1 (m1: mTest1 nat bool) :=
  match m1 with
  | cmTest11 _ => I
  | cmTest12 _ a b c => I
  | cmTest13 _ a => I
  end.

Effect Translate match1.

Inductive even: nat -> Prop :=
| evZ: even 0
| evS: forall n, odd n -> even (S n)
with
odd: nat -> Prop :=
| oddS: forall n, even n -> odd (S n).

Effect Translate even.

Inductive listP (A: Type): Prop :=
  nilP : listP A | consP : A -> list A -> listP A.
Effect Translate listP.

Inductive test (A: Type) (B: Prop) (b: B) (a: A): A -> B -> Type := .

Effect Translate test.

Definition id (A: Type) := A.
Effect Translate id.

Definition idT := id Type.
Effect Translate idT.

Definition ind_test := mTest4.
Effect Translate ind_test.


Definition b1 := Type.
Effect Translate b1.

Definition b2 := fun A: Type => A.
Effect Translate b2.

Definition b3 (A: Type) (B: Prop): A -> B -> B := fun _ c => c.
Effect Translate b3.

Definition b4 (A: Type) (B: Prop): A -> B -> A := fun c _ => c.
Effect Translate b4.

Definition t1 := Type.
Effect Translate t1.
Definition t2 (A: Type) := Type.
Effect Translate t2.

Definition t3 (A: Type) := True.
Effect Translate t3.

Definition t4 : Type -> Prop -> Prop := fun _ _ => True.
Effect Translate t4.

Definition t5 (A: Type) : A  -> Type := fun _ => Type.
Effect Translate t5.

Definition t6 (A: Type) (B: Prop) (C: Type): A -> B -> B -> Prop := fun _ _ _ => True.
Effect Translate t6.

Definition t7 (A: Type) (P: Type -> Type): P A -> Type := fun _ => Type.
Effect Translate t7.

Definition t8 (A: Prop): (fun a: Type => a) Prop -> Prop := fun _ => True.
Effect Translate t8.

Definition t9 (A: Type) (B: Prop) (P: A -> B -> Prop) (a: A) (b: B): P a b -> Prop := fun _ => True.
Effect Translate t9.

Definition t10 (A: Prop): (fun a: Type => a) Prop -> Type := fun _ => True.
Fail Effect Translate t10. (* Because of cumulative prohibition in the target *)
