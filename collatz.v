From SMTCoq Require Import SMTCoq.

Inductive N : Type :=
  | z : N
  | S : N -> N.

Inductive N' : Type :=
  | one : N'
  | S1 : N' -> N'
  | S2 : N' -> N'.

Fixpoint add (n m : N) :=
  match n with
  | z => m
  | S p => S (add p m)
  end.

Fixpoint mul (n m : N) :=
  match n with
  | z => z
  | S p => add m (mul p m)
  end.

Fixpoint divmod x y q u :=
  match x with
    | z => (q,u)
    | S x' => match u with
                | z => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition div x y :=
  match y with
    | z => y
    | S y' => fst (divmod x y' z y')
  end.

Fixpoint even n : bool :=
  match n with
    | z => true
    | (S z) => false
    | S (S n') => even n'
  end.


Definition pred (n:N) : N := match n with
                                 | z => z
                                 | S u => u
                                 end.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Fixpoint N'toN x :=
  match x with
    | one => S z
    | S1 x' => mul (N'toN x') (S (S z))
    | S2 x' => div (pred (N'toN x')) (S (S (S z)))
  end.

Definition mN'toN x : option N := 
  match x with
    | None _ => None _
    | Some _ y => Some _ (N'toN y)
  end. 

(* Fixpoint mN'toN : option N' -> option N := 
  fun x => match x with 
    | Some _ one => None _
    | Some _ (S1 y) => match (mN'toN y) with | None _ => None _ | Some _ y' => Some _ (mul y' (S (S z))) end
    | Some _ (S2 y) => match (mN'toN y) with | None _ => None _ | Some _ y' => Some _ (div (pred y') (S (S (S z)))) end
  end. *)
(* 
Definition conversionDecidable (parNtoN' : N -> option N') :=
  forall y, 
    ((exists (y' : N') , Some _ y' = parNtoN' y /\ parNtoN' y = match y with
      | z => Some _ z'
      | S z => Some _ one
      | S (S y') => match (even (S (S y'))) with
                  | true => match (parNtoN' (div (S (S y')) (S (S z)))) with | Some _ x => Some _ (S1 x) | None _ => None _ end
                  | false => match (parNtoN' (add (mul (S (S (S z))) (S (S y'))) (S z))) with | Some _ x => Some _ (S2 x) | None _ => None _ end
                end
    end) <-> parNtoN' y <> None _). *)

Definition Niso : forall NtoN',  (forall y,  (NtoN' y = match y with
    | z => one
    | S z => one
    | S (S y') => match (even (S (S y'))) with
                | true => S1 (NtoN' (div (S (S y')) (S (S z))))
                | false => S2 (NtoN' (add (mul (S (S (S z))) (S (S y'))) (S z)))
              end
  end)) 
  -> (forall mNtoN', (forall x, mNtoN' x = match x with 
    | None _ => None _
    | Some _ z => None _
    | Some _ (S y) => Some _ (NtoN' (S y))
  end) -> 
  forall x, mNtoN' (mN'toN x) = x).
intros NtoN' H mNtoN'. intro defmNtoN'. intro x. induction x. induction a. 
generalize (H (S z)). intro. 
generalize (defmNtoN' (mN'toN (Some _ one))). intro.
rewrite H1. assert ((mN'toN (Some N' one)) = (mN'toN (Some N' (NtoN' (S z))))).
unfold mN'toN.
rewrite H0. auto.
unfold mN'toN. unfold N'toN.
rewrite H0. auto.
unfold mN'toN. 
generalize (defmNtoN' ((Some N (N'toN (S1 a))))). intro. rewrite H0.
simpl. generalize (H (N'toN a)). simpl. intro. 
rewrite (H (S y)).
rewrite H0. auto.
 rewrite H2. simpl.

 induction (mN'toN (Some N' one)).
simpl.
compute. auto. 
(* generalize (H (S z)). intro. simpl. apply H0. intro. inversion H1.  *)
generalize (H  (N'toN (S1 a))). simpl.
intros. auto.
generalize (H  (N'toN (S2 x))). simpl.
intros. auto.

Definition Niso : forall NtoN',  (forall y,  (NtoN' y = match y with
    | z => one
    | S z => one
    | S (S y') => match (even (S (S y'))) with
                | true => S1 (NtoN' (div (S (S y')) (S (S z))))
                | false => S2 (NtoN' (add (mul (S (S (S z))) (S (S y'))) (S z)))
              end
  end)) 
  -> (forall mNtoN', (forall x, mNtoN' x = match x with 
    | None _ => None _
    | Some _ z => None _
    | Some _ (S y) => Some _ (NtoN' (S y))
  end) -> 
  forall x, mN'toN (mNtoN' x) = x).
intros NtoN' H mNtoN' defmNtoN' x. induction x. 
generalize (defmNtoN' (Some _ )). intro. 
compute. apply H0.
(* generalize (H (S z)). intro. simpl. apply H0. intro. inversion H1.  *)
generalize (H  (N'toN (S1 x))). simpl.
intros. auto.
generalize (H  (N'toN (S2 x))). simpl.
intros. auto.

Definition nonotExMap : ~ (forall NtoN', ~ forall x, N'toN (NtoN' x) = x).
intro. 
assert (forall NtoN',  (forall y, NtoN' y = match y with
    | z => z'
    | S z => one
    | S (S y') => match (even (S (S y'))) with
                | true => S1 (NtoN' (div (S (S y')) (S (S z))))
                | false => S2 (NtoN' (add (mul (S (S (S z))) (S (S y'))) (S z)))
              end
  end) -> (forall x : N, N'toN (NtoN' x) = x)).
intros. generalize (H0 x). induction x. 
destruct (NtoN' z); auto; compute; intro; inversion H1.
generalize (H0 x). intro. generalize (IHx H1). intros.
assert (forall a, a = S (N'toN (NtoN' x)) -> a = S x).
intros. rewrite <- H2. auto. rewrite (H4 (N'toN (NtoN' (S x)))). auto.
rewrite H3.
compute.
assert (N'toN (NtoN' (S x)) = S (N'toN (NtoN' x))). auto.
assert (N'toN (S (NtoN' x)) = S x).
rewrite <- H2.
rewrite H3. simpl. induction (match x with
  | z => one
  | S y' =>
      if even y'
      then S1 (NtoN' (fst (divmod y' (S z) (S z) (S z))))
      else
       S2
         (NtoN' (S (S (add (add y' (S (S (add y' (S (S (add y' z))))))) (S z)))))
  end). compute.
unfold N'toN. simpl.
simpl. simpl. compute; auto.

Definition existsParNtoN' := exists parNtoN', conversionDecidable parNtoN'.

Definition forallParNtoN' : forall parNtoN', conversionDecidable parNtoN' -> 
  forall x, x <> z -> N'toN (match (parNtoN' x) with | Some _ y => y | None _ => z' end) = x.
intros. unfold conversionDecidable in H. induction x. assert (z = z). 
auto. generalize (H0 H1). intro. elim H2. generalize (H (S x)).
simpl. intro. elim H1. intro. intro. 
assert (parNtoN' (S x) <> None N'). Focus 2.
generalize (H3 H4).
intro. destruct H5. destruct H5. rewrite H6. destruct x0. compute. 
assert (S (N'toN
        match parNtoN' x with
        | Some _ y => y
        | None _ => z'
        end) = S (x)).

assert (N'toN
        match parNtoN' x with
        | Some _ y => y
        | None _ => z'
        end = x). apply IHx.

induction x. 
. apply H0.
generalize (H x).  inversion H0.

Definition collatz : forall NtoN', (forall y, y <> z -> ((NtoN' y <> z') <->
  NtoN' y = match y with
    | z => z'
    | S z => one
    | S (S y') => match (even (S (S y'))) with
                | true => S1 (NtoN' (div (S (S y')) (S (S z))))
                | false => S2 (NtoN' (add (mul (S (S (S z))) (S (S y'))) (S z)))
              end
  end)) -> ((forall x, ~(x = z') -> (NtoN' (N'toN x)) = x) /\
              (forall x, ~(x = z) -> (N'toN (NtoN' x)) = x)).
  intros NtoN' H.
  split.
  - intros x Hx.
    induction x. destruct Hx. auto. compute.
    generalize (H (S z)). compute. intros.
  


