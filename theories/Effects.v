Declare ML Module "exception".

Set Universe Polymorphism.
Set Primitive Projections.

Inductive any@{i} : Type@{i} := Any.

Cumulative Inductive type@{i j} (E : Type@{i}) : Type :=
| TypeVal : forall (A : Type@{j}), (E -> A) -> type E
| TypeErr : E -> type E.

Definition El@{i j} {E : Type@{i}} (A : type@{i j} E) : Type@{j} :=
match A with
| TypeVal _ A _ => A
| TypeErr _ e => any@{j}
end.

Definition Err@{i j} {E : Type@{i}} (A : type@{i j} E) : E -> El@{i j} A :=
match A return E -> El A with
| TypeVal _ _ e => e
| TypeErr _ _ => fun _ => Any
end.

Definition Typeᵉ@{i j k} (E : Type@{i}) : type@{i k} E :=
  TypeVal E (type@{i j} E) (TypeErr E).

Definition Propᵉ@{i j} (E: Type@{i}): type@{i j} E :=
  TypeVal E Prop (fun _ => True).

Arguments Typeᵉ {_}.

Definition Prodᵉ@{i j k l} (E : Type@{i}) (A : Type@{j})
  (B : A -> type@{i k} E) : type@{i l} E :=
  TypeVal E (forall x : A, El (B x)) (fun e x => Err (B x) e).

Axiom Exception: Type.
Definition Exceptionᵉ (E: Type): type E := TypeVal E E (fun e => e).
Axiom raise: forall (A: Type), Exception -> A.
Definition raiseᵉ (E: Type) (A: @El E (@Typeᵉ E)) (e: @El E (Exceptionᵉ E)) := Err A e.

Inductive Falseᵒ (E: Type): Prop :=.

Set Primitive Projections.
Class Param (A: Type) := {
  param: A -> Prop;
  param_correct: forall e, param (raise A e) -> False
}.

Class Paramᵉ (E: Type) (A: @El E (@Typeᵉ E)) := {
  paramᵉ: @El E A -> Prop;
  param_correctᵉ: forall e, paramᵉ (raiseᵉ E A e) -> (Falseᵒ E)
}.
Unset Primitive Projections.
