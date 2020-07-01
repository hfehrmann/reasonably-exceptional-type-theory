Require Import Effects.Exception.

Inductive inductive_with_prop (A: Prop): Type :=
| cons_inductive_with_prop: A -> inductive_with_prop A.

Effect Translate inductive_with_prop.

Inductive index_test (A: Type): A -> Type :=
| cons_index_tsst: forall a, index_test A a.

Effect Translate index_test.

Inductive vec (A: Type): nat -> Type :=
| vnil: vec A 0
| vcons: forall n, vec A n -> A -> vec A (S n).

Inductive plop: nat -> Type :=
| plop1: plop 0
| plop2: forall n, plop n -> nat -> plop (S n).

Fixpoint f n :=
  match n with
  | O => 0
  | S m => S (S (f m))
  end.

Definition F :=
  fun (A: Type) (m: nat) =>
    fix f (_ _: nat) (l: list A) {struct l}: nat :=
    match l with
    | nil => 0
    | cons _ ll => S (S (f 0 0 ll)) + m
    end.

Effect Translate nat.
Effect Translate list.
Effect Translate Nat.add.
Effect Translate f.
Effect Translate F.
Effect Translate plop.
Effect Translate vec.
Effect Translate bool.
Effect Translate False.


Inductive ll: Type -> Type := ll_: forall A, ll A.
Print ll_rect. Effect Translate ll. Effect Translate ll_rect.
Print ll_rect.

Inductive test (A: Type) (a: nat): nat ->  bool -> Type :=
| test1: test A a 0 false -> test A a 0 false
(* | test1: test A a 0 false *)
| test2: forall n, test A a n true -> test A a (S n) false
| test4: forall n b1, test A a n b1 -> (forall m b2, test A a m b2) -> test A a n b1
| test5: forall (f: nat -> Type), f 1 -> test A a 1 true.

Effect Translate test.
Print test_rect.
Effect Translate test_rect.
Print test_rectᵉ.
Print test_catchᵉ.
Print vec_ind_paramᵉ.

Inductive my_sum (A B : Prop) : Type :=  my_inl : A -> my_sum A B | my_inr : B -> my_sum A B.

Notation "A ++ B" := (my_sum A B) : type_scope.
Arguments my_inl {_ _} _.
Arguments my_inr {_ _} _.

Effect List Translate my_sum my_sum_rect my_sum_rec.
Effect List Translate sum sum_rect sum_rec.
Effect List Translate True True_ind True_rect False_ind False_rect not.
Effect List Translate eq eq_ind eq_rect eq_rec.
Effect List Translate length eq_sym eq_trans f_equal.
Effect List Translate sig sig_rect sig_rec proj1_sig.
Effect List Translate prod prod_rect.

(* basic inversion lemmas for nat *)

Effect Definition S_not0 : forall n, 0 <> S n.
Proof.
  cbn; intros e n H. inversion H.
Defined.

Effect Definition inj_S : forall n m, S n = S m -> n = m.
intros E n m e. inversion e; econstructor.
Defined.
