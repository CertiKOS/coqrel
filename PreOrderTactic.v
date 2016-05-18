Require Import RelDefinitions.

(** The following tactic attempts to prove a relational goal by
  combining the [reflexivity] and [transitivity] properties of
  preorders with hypotheses available in the context. This is
  implemented through a simple depth-first search as follows.
  Assuming the goal is [R m n], we use [m] as the starting node.
  We maintain a stack of terms with proofs that they are related
  to [m], initialized with [(m, reflexivity)::nil]. Then as long
  as the stack is non-empty:

    - Pop the first element [(t, Ht)].
    - If [t] is [n], success! Use [Ht].
    - Otherwise, for every hypothesis of the form [Ht': R t t'],
      push (t', transitivity m t t' Ht Ht') on the stack.

  If the search terminates without encountering [n], fail. Once a
  hypothesis has been used, it is "deactivated" so as not to be used
  again, using the following marker. *)

Definition preorder_tactic_done {A B} (R: rel A B) a b := R a b.

Ltac preorder :=
  lazymatch goal with
    | |- ?R ?m ?n =>
      let HR := fresh "HR" in
      first
        [ assert (HR: PreOrder R) by typeclasses eauto
        | fail 1 R "is not a declared preorder" ];
      let rec step q :=
        lazymatch q with
          | cons (exist _ n ?Hn) _ =>
            exact Hn
          | cons (exist _ ?t ?Ht) ?tail =>
            gather tail t Ht
        end
      with gather q t Ht :=
        lazymatch goal with
          | Ht': R t ?t' |- _ =>
            change (preorder_tactic_done R t t') in Ht';
            gather (cons (exist (R m) t' (transitivity Ht Ht')) q) t Ht
          | _ =>
            step q
        end in
      first
        [ step (cons (exist (R m) m (reflexivity m)) nil)
        | fail 1 n "not reachable from" m "using hypotheses from the context" ]
    | _ =>
      fail "the goal is not an applied relation"
  end.

(** Hook [preorder] for providing [RStep]s *)

Hint Extern 30 (RStep ?P (_ _ _)) =>
  try unify P True; intro; preorder : typeclass_instances.
