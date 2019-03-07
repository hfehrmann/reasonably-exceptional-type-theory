Require Import Weakly.Effects.

Inductive sum (A B : Prop) : Type :=  inl : A -> sum A B | inr : B -> sum A B.

Notation "A + B" := (sum A B) : type_scope.
Arguments inl {_ _} _.
Arguments inr {_ _} _.

Effect List Translate sum sum_rect sum_rec. 
Effect List Translate True True_ind True_rect False False_ind False_rect not.
Effect List Translate eq eq_ind eq_rect eq_rec.
Effect List Translate nat nat_rect nat_rec. 
Effect List Translate list list_rect.
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

(* Decidable type class *)

Class Decidable (A : Prop) : Type := dec : A + (not A).
Effect Translate Decidable.
Effect Translate dec.
  
Arguments dec A {_}.

Class EqDecidable (A : Type) := { eq_dec : forall a b : A, Decidable (a = b) }.
Effect Translate EqDecidable.

Instance Decidable_eq_nat : forall (x y : nat), Decidable (x = y).
induction x.
- induction y.
  + left. apply eq_refl.
  + right. apply S_not0. 
- induction y.
  + right. intro H. symmetry in H. destruct (S_not0 _ H).
  + induction (IHx y). left. f_equal; auto. 
    right. intro e. apply inj_S in e. apply (b e).
Defined.
Effect List Translate Decidable_eq_nat.

Instance EqDecidable_nat : EqDecidable nat := { eq_dec := Decidable_eq_nat }.
Effect List Translate EqDecidable_nat.

Instance FalseDecidable : Decidable False.
Proof. right; intros a; assumption. Defined.
Effect Translate FalseDecidable.
  
Notation " ( x ; p ) " := (exist _ x p).

Definition cast (e: Exception) (A:Type) (P : A -> Prop)
           (a:A) {Hdec : Decidable (P a)} : {a : A | P a}.
  induction (dec (P a)) using sum_rect. 
  - exact (a ; a0).
  - exact (raise _ e).
Defined. 
Effect Translate cast.

Definition forbidden_cast e: False := proj2_sig (cast e nat (fun _ => False) 0).
Fail Effect Translate proj2_sig. 
(* Due to elimination from Prop to Type *)
(* ==> Fail Effect Translate forbidden_cast. *)

Definition list2_to_pair {A} : {l : list A | length l = 2} -> A * A.
Proof.
  induction 1. induction x.
  - induction (S_not0 _ p) using False_rect.
  - induction x.
    + apply inj_S in p. induction (S_not0 _ p) using False_rect.
    + exact (a , a0).
Defined.
Effect Translate list2_to_pair.

Definition list_to_pair (e: Exception) {A} : list A -> A * A.
Proof.
  exact (fun l => list2_to_pair (cast e (list A) (fun l => length l = 2) l)).  
Defined.
Effect Translate list_to_pair.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) : list_scope.
Open Scope list_scope.

Definition list_to_pair_prop A (x : A) e : list_to_pair e [x ; raise _ e] = (x, raise _ e).
Proof.
  reflexivity.
Defined.

Effect Translate list_to_pair_prop.

(* sanity check *)

Definition list_to_pair_prop_soundness E A x y :
  list_to_pair_propᵉ E A x y = eq_reflᵉ  _ _ _ := eq_refl. 

(* those two examples should be forbidden, because of non cummulativity *)

Effect Definition list_to_pair_prop_fake : forall A (x y : A) e,
    list_to_pair e (raise _ e) = (x,y) -> False.
Proof.
  intros E A x y e H.
  inversion H.
Defined.  

Effect Definition list_to_pair_prop_fake2 : forall A (x y : A) e,
    list_to_pair e [x;y;y] = (x,y) -> False.
Proof.
  intros E A x y e H.
  inversion H.
Defined.


(* TOY LANGUAGE *)
Inductive binop : Set := Plus | Minus | Times.

Inductive exp: Set :=
| Const: nat -> exp
| Binop: binop -> exp -> exp -> exp.

Fixpoint evalBinop (e: binop): nat -> nat -> nat :=
  match e with
  | Plus => plus
  | Minus => Nat.sub
  | Times => Nat.mul
  end.

Fixpoint evalExp (e: exp): nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (evalBinop b) (evalExp e1) (evalExp e2)
  end.

Inductive instr: Set :=
| iConst: nat -> instr
| iBinop: binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition runInstr e (i: instr) (s: stack): option stack :=
  match i with
  | iConst j => Some (j :: s)
  | iBinop b => match s with
                | arg1 :: arg2 :: s' => Some ((evalBinop b) arg1 arg2::s')
                | _ => raise _ e
                end
  end. 

Fixpoint runProg e (p: prog) (s: stack): option stack :=
  match p with
    | nil => Some s
    | i::p' => match runInstr e i s with
               | None => None
               | Some s' => runProg e p' s'
               end
  end.

Fixpoint compile (e: Exception) (exp_term: exp): prog :=
  match exp_term with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e e1 ++ compile e e2 ++ iBinop b :: nil
end.
Effect List Translate Nat.add Nat.sub Nat.mul.
Effect List Translate app.
Effect List Translate option.
Effect List Translate 
       binop exp evalBinop evalExp instr prog stack runInstr runProg compile.

Print compileᵉ.

Theorem compile_correct: forall e exp_term,
    runProg e (compile e exp_term) nil = Some (evalExp exp_term :: nil).